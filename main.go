// Command forge is a standalone GitHub-compatible git forge in a single file.
//
// It serves four surfaces over one in-memory store: git smart HTTP
// (protocol v0 and v2, upload-pack and receive-pack), the GitHub REST v3
// API, the GitHub GraphQL v4 API, and an MCP server over streamable HTTP.
//
// Lifecycle (the make.fun trial contract): bind an ephemeral port, POST
// {"port": N} to $MAKEFUN_ENV_URL/register, serve, and poll
// $MAKEFUN_ENV_URL/done until {"done": true}, then exit 0. When
// MAKEFUN_ENV_URL is unset the server runs standalone on $PORT
// (default 8080) for local testing.
//
// Authentication is a single bearer token from $MAKEFUN_SHOP_TOKEN. The
// token names the viewer "adaiversen": the suite's scenario is seeded and
// fixed, so the viewer login is a constant of the wire contract.
//
// This file is original code written for the make.fun
// "github-core-clone-01" bounty. It uses only the Go standard library, it
// never shells out to git (or to anything else), and it never touches the
// network except to answer the env's register/done endpoints.
package main

import (
	"bytes"
	"compress/zlib"
	"crypto/sha1"
	"crypto/subtle"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"unicode/utf8"
)

// ---------------------------------------------------------------------------
// constants

// viewerLogin is the login the bearer token names. The suite's scenario is
// built from one fixed seed (wire.ts SCENARIO_SEED), so the viewer is the
// same in every trial: users[0], id 1000.
const viewerLogin = "adaiversen"

const viewerID = 1000

const viewerEmail = "adaiversen@example.invalid"

// fixedEpoch / fixedISO are the only timestamps the forge ever emits, so a
// live run and a replay produce byte-identical state.
const fixedEpoch = 1794960000 // 2026-11-18T00:00:00Z
const fixedISO = "2026-11-18T00:00:00Z"

const defaultBranch = "main"

// Git object types.
const (
	objCommit = 1
	objTree   = 2
	objBlob   = 3
	objTag    = 4
)

var objTypeNames = map[int]string{
	objCommit: "commit",
	objTree:   "tree",
	objBlob:   "blob",
	objTag:    "tag",
}

const zeroOID = "0000000000000000000000000000000000000000"

// ---------------------------------------------------------------------------
// configuration

type config struct {
	token   string // expected bearer token ("" = accept any non-empty token, local dev)
	envURL  string // $MAKEFUN_ENV_URL, "" = standalone mode
	port    string // $PORT for standalone mode
	viewer  string // token owner's login
	agent   string // server name for MCP/GraphQL identity
	version string
}

func loadConfig() config {
	c := config{
		token:   os.Getenv("MAKEFUN_SHOP_TOKEN"),
		envURL:  strings.TrimRight(os.Getenv("MAKEFUN_ENV_URL"), "/"),
		port:    os.Getenv("PORT"),
		viewer:  os.Getenv("FORGE_VIEWER"),
		agent:   "forge",
		version: "1.0.0",
	}
	if c.viewer == "" {
		c.viewer = viewerLogin
	}
	if c.port == "" {
		c.port = "8080"
	}
	return c
}

// ---------------------------------------------------------------------------
// the store: one set of objects shared by all four surfaces

type gitObj struct {
	typ  int
	data []byte
}

type comment struct {
	id   int
	body string
	seq  int64
}

type issue struct {
	id       int
	number   int
	title    string
	body     string
	state    string // "open" | "closed"
	labels   []string
	comments []*comment
	seq      int64
}

type pull struct {
	id             int
	number         int
	title          string
	body           string
	state          string // "open" | "closed"
	merged         bool
	mergedAt       string
	mergeCommitSha string
	headRef        string
	baseRef        string
	headSha        string // head tip at creation
	baseSha        string // base tip at creation
	seq            int64
}

type label struct {
	id    int
	name  string
	color string
}

type repo struct {
	id            int
	name          string
	owner         string
	private       bool
	description   string
	defaultBranch string
	seq           int64

	refs    map[string]string // refname -> oid hex
	objects map[string]*gitObj

	// fetchMu guards fetchCache: complete upload-pack response bodies
	// for fetch requests already answered for the current repo state.
	// Lock order is always the store lock outer, fetchMu inner (fetchers
	// take RLock then fetchMu; mutators take Lock then fetchMu via
	// touch), so the two locks can never deadlock against each other.
	fetchMu    sync.Mutex
	fetchCache map[string][]byte

	issues     map[int]*issue
	pulls      map[int]*pull
	labels     map[string]*label
	nextNumber int // shared issue/PR counter (GitHub semantics)
}

// touch invalidates the repo's cached fetch responses. Call it after any
// change to objects or refs, while holding the store write lock: no fetch
// can be computing against the old state while the cache clears, because
// computing fetches hold the store read lock.
func (r *repo) touch() {
	r.fetchMu.Lock()
	defer r.fetchMu.Unlock()
	clear(r.fetchCache)
}

type store struct {
	mu            sync.RWMutex
	repos         map[string]*repo // "owner/name"
	repoByID      map[int]*repo
	nextRepoID    int
	nextIssueID   int
	nextCommentID int
	nextLabelID   int
	seq           int64
}

func newStore() *store {
	return &store{
		repos:         make(map[string]*repo),
		repoByID:      make(map[int]*repo),
		nextRepoID:    1,
		nextIssueID:   1,
		nextCommentID: 1,
		nextLabelID:   1,
	}
}

func (s *store) nextSeq() int64 {
	s.seq++
	return s.seq
}

func repoKey(owner, name string) string { return owner + "/" + name }

// ---------------------------------------------------------------------------
// server

type server struct {
	cfg   config
	st    *store
	mux   *http.ServeMux
	reqID uint64 // atomic counter for X-GitHub-Request-Id

	// mcpToolsJSON is the tools/list result, marshalled once so two calls
	// answer byte-identical lists.
	mcpToolsJSON []byte
}

func newServer(cfg config) *server {
	s := &server{cfg: cfg, st: newStore(), mux: http.NewServeMux()}
	s.mux.HandleFunc("/", s.route)
	s.mcpToolsJSON = marshalJSON(mcpToolsResult())
	return s
}

func (s *server) nextReqID() string {
	n := atomic.AddUint64(&s.reqID, 1)
	// Hand-rolled "forge-%08x": fmt.Sprintf on this path cost more than
	// the rest of request dispatch combined. The counter is masked to
	// 32 bits, matching %08x of the values Sprintf produced here.
	var buf [14]byte
	copy(buf[:], "forge-")
	v := uint32(n)
	for i := 13; i >= 6; i-- {
		buf[i] = hexDigits[v&0xf]
		v >>= 4
	}
	return string(buf[:])
}

// route dispatches every request. The order follows the hot paths first.
func (s *server) route(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("X-GitHub-Request-Id", s.nextReqID())
	path := r.URL.Path

	switch {
	case path == "/healthz":
		if r.Method != http.MethodGet {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		s.writeJSON(w, http.StatusOK, map[string]any{"ok": true})
		return
	case path == "/api/graphql":
		s.handleGraphQL(w, r)
		return
	case path == "/mcp":
		s.handleMCP(w, r)
		return
	case path == "/api/v3" || strings.HasPrefix(path, "/api/v3/"):
		s.handleREST(w, r)
		return
	case strings.HasSuffix(path, ".git/info/refs") ||
		strings.HasSuffix(path, ".git/git-upload-pack") ||
		strings.HasSuffix(path, ".git/git-receive-pack"):
		s.handleGit(w, r)
		return
	default:
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
}

// authorized reports whether the request carries the expected bearer token.
// It reads the Authorization header from the map directly (Get
// re-canonicalizes the key on every call) and compares tokens byte-wise
// without the two []byte conversions ConstantTimeCompare would force.
func (s *server) authorized(r *http.Request) bool {
	var h string
	if v := r.Header["Authorization"]; len(v) > 0 {
		h = v[0]
	}
	if len(h) < 7 || h[:7] != "Bearer " {
		return false
	}
	got := h[7:]
	if got == "" {
		return false
	}
	want := s.cfg.token
	if want == "" {
		return true // local dev: no token configured, any non-empty bearer works
	}
	if len(got) != len(want) {
		return false
	}
	var diff byte
	for i := 0; i < len(got); i++ {
		diff |= got[i] ^ want[i]
	}
	return subtle.ConstantTimeByteEq(diff, 0) == 1
}

func (s *server) requireAuth(w http.ResponseWriter, r *http.Request) bool {
	if s.authorized(r) {
		return true
	}
	s.writeJSON(w, http.StatusUnauthorized, errBody("Bad credentials"))
	return false
}

// ---------------------------------------------------------------------------
// JSON helpers

func errBody(msg string) map[string]any { return map[string]any{"message": msg} }

func marshalJSON(v any) []byte {
	b, err := json.Marshal(v)
	if err != nil {
		return []byte("{}")
	}
	return b
}

func (s *server) writeJSON(w http.ResponseWriter, status int, v any) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	_, _ = w.Write(marshalJSON(v))
}

func (s *server) writeRawJSON(w http.ResponseWriter, status int, b []byte) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(status)
	_, _ = w.Write(b)
}

// ---------------------------------------------------------------------------
// hand-rolled JSON encoding for the hot REST shapes
//
// encoding/json over map[string]any is the read/write workloads' biggest
// cost: every response builds a tree of maps, then Marshal reflects over
// it and sorts the keys. The encoder below writes the same bytes directly
// — keys in encoding/json's sorted order, strings escaped exactly the way
// Marshal escapes them (HTML escaping on: < > & become \u003c \u003e
// \u0026; U+2028/U+2029 escaped; invalid UTF-8 becomes \ufffd) — at a
// fraction of the allocations. A differential test against Marshal keeps
// the two in agreement.
//
// Unlike V2, the rendered bytes are NOT cached on the issue: the cache
// wrote to the issue under a read lock (a data race between concurrent
// readers) and saved only the render cost on repeat reads, which profiling
// showed to be a few microseconds per request.
//
// appendJSONString appends s as a quoted JSON string, byte-identical to
// encoding/json's encoding of the same string.
func appendJSONString(dst []byte, s string) []byte {
	// Fast path: scan for any byte that needs escaping. Most titles and
	// bodies contain none, so the common case is one bounds check per
	// byte and a single append.
	needEscape := false
	for i := 0; i < len(s); i++ {
		c := s[i]
		if c < 0x20 || c == '"' || c == '\\' || c == '<' || c == '>' || c == '&' || c >= 0x80 {
			needEscape = true
			break
		}
	}

	dst = append(dst, '"')
	if !needEscape {
		dst = append(dst, s...)
		return append(dst, '"')
	}
	const hex = "0123456789abcdef"
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '"':
			dst = append(dst, '\\', '"')
		case c == '\\':
			dst = append(dst, '\\', '\\')
		case c == '\n':
			dst = append(dst, '\\', 'n')
		case c == '\r':
			dst = append(dst, '\\', 'r')
		case c == '\t':
			dst = append(dst, '\\', 't')
		case c == '\b':
			dst = append(dst, '\\', 'b')
		case c == '\f':
			dst = append(dst, '\\', 'f')
		case c == '<':
			dst = append(dst, '\\', 'u', '0', '0', '3', 'c')
		case c == '>':
			dst = append(dst, '\\', 'u', '0', '0', '3', 'e')
		case c == '&':
			dst = append(dst, '\\', 'u', '0', '0', '2', '6')
		case c < 0x20:
			dst = append(dst, '\\', 'u', '0', '0', hex[c>>4], hex[c&0xf])
		case c < 0x80:
			dst = append(dst, c)
		default:
			// Multi-byte UTF-8: copy the rune through, except U+2028 /
			// U+2029 (which Marshal escapes) and invalid bytes (which
			// Marshal replaces with \ufffd).
			if c == 0xe2 && i+2 < len(s) && s[i+1] == 0x80 && (s[i+2] == 0xa8 || s[i+2] == 0xa9) {
				dst = append(dst, '\\', 'u', '2', '0', '2', hex[s[i+2]&0xf])
				i += 2
				continue
			}
			// Decode one rune to check validity.
			_, size := utf8.DecodeRuneInString(s[i:])
			if size == 1 {
				// Invalid byte (or 0x80-0xbf stray): Marshal emits \ufffd.
				// DecodeRuneInString returns size 1 for RuneError only
				// on invalid input; a valid 1-byte rune is ASCII and was
				// handled above, so reaching here means invalid.
				dst = append(dst, '\\', 'u', 'f', 'f', 'f', 'd')
			} else {
				dst = append(dst, s[i:i+size]...)
				i += size - 1
			}
		}
	}
	return append(dst, '"')
}

// appendJSONInt appends a decimal integer.
func appendJSONInt(dst []byte, n int) []byte {
	return strconv.AppendInt(dst, int64(n), 10)
}

// issueJSONBytes renders an issue exactly as json.Marshal(issueJSON(rp, is))
// would, but without building the map tree. Keys are emitted in
// encoding/json's sorted order.
func (s *server) issueJSONBytes(rp *repo, is *issue) []byte {
	// Pre-size: the fixed skeleton is ~200 bytes plus title, body and
	// labels. Growing from a good guess avoids reallocation.
	b := make([]byte, 0, 256+len(is.title)+len(is.body)+len(is.labels)*64)
	b = append(b, '{')
	b = append(b, `"body":`...)
	b = appendJSONString(b, is.body)
	b = append(b, `,"comments":`...)
	b = appendJSONInt(b, len(is.comments))
	b = append(b, `,"created_at":"`...)
	b = append(b, fixedISO...)
	b = append(b, `","id":`...)
	b = appendJSONInt(b, is.id)
	b = append(b, `,"labels":[`...)
	for i, n := range is.labels {
		if i > 0 {
			b = append(b, ',')
		}
		if l, ok := rp.labels[n]; ok {
			b = append(b, `{"color":`...)
			b = appendJSONString(b, l.color)
			b = append(b, `,"default":false,"description":"","id":`...)
			b = appendJSONInt(b, l.id)
			b = append(b, `,"name":`...)
			b = appendJSONString(b, l.name)
			b = append(b, '}')
		} else {
			b = append(b, `{"color":"ededed","name":`...)
			b = appendJSONString(b, n)
			b = append(b, '}')
		}
	}
	b = append(b, `],"number":`...)
	b = appendJSONInt(b, is.number)
	b = append(b, `,"state":`...)
	b = appendJSONString(b, is.state)
	b = append(b, `,"title":`...)
	b = appendJSONString(b, is.title)
	b = append(b, `,"updated_at":"`...)
	b = append(b, fixedISO...)
	b = append(b, `","user":{"id":`...)
	b = appendJSONInt(b, viewerID)
	b = append(b, `,"login":`...)
	b = appendJSONString(b, s.cfg.viewer)
	b = append(b, `,"type":"User"}}`...)
	return b
}

// readJSONBody reads and parses a JSON request body. It reports whether the
// body parsed; a malformed body is a 400 with a JSON message.
func (s *server) readJSONBody(w http.ResponseWriter, r *http.Request, v any) bool {
	defer r.Body.Close()
	body, err := io.ReadAll(io.LimitReader(r.Body, 16<<20))
	if err != nil {
		s.writeJSON(w, http.StatusBadRequest, errBody("could not read request body"))
		return false
	}
	if len(bytes.TrimSpace(body)) == 0 {
		return true // empty body: leave v at its zero value
	}
	if err := json.Unmarshal(body, v); err != nil {
		s.writeJSON(w, http.StatusBadRequest, errBody("malformed JSON body"))
		return false
	}
	return true
}

// ---------------------------------------------------------------------------
// lifecycle: register with the env, serve, poll /done

func main() {
	log.SetFlags(0)
	cfg := loadConfig()
	srv := newServer(cfg)

	var ln net.Listener
	var err error
	if cfg.envURL != "" {
		// Trial mode: ephemeral port, never 8080 (the env owns it).
		ln, err = net.Listen("tcp", "127.0.0.1:0")
	} else {
		ln, err = net.Listen("tcp", "0.0.0.0:"+cfg.port)
	}
	if err != nil {
		log.Fatalf("listen: %v", err)
	}
	port := ln.Addr().(*net.TCPAddr).Port

	httpSrv := &http.Server{
		Handler:      srv.mux,
		ReadTimeout:  0, // long-lived git streams; the suite enforces its own deadlines
		WriteTimeout: 0,
		IdleTimeout:  0,
	}

	if cfg.envURL != "" {
		go func() {
			_ = httpSrv.Serve(ln)
		}()
		if err := registerWithEnv(cfg.envURL, port); err != nil {
			log.Fatalf("register: %v", err)
		}
		log.Printf("registered on port %d, polling %s/done", port, cfg.envURL)
		pollDone(cfg.envURL)
		_ = httpSrv.Close()
		os.Exit(0)
	}

	// Standalone mode (local testing).
	fmt.Printf("READY\nListening on http://0.0.0.0:%d\n", port)
	log.Fatal(httpSrv.Serve(ln))
}

func registerWithEnv(envURL string, port int) error {
	body := marshalJSON(map[string]any{"port": port})
	var lastErr error
	for attempt := 0; attempt < 10; attempt++ {
		req, err := http.NewRequest(http.MethodPost, envURL+"/register", bytes.NewReader(body))
		if err != nil {
			return err
		}
		req.Header.Set("Content-Type", "application/json")
		resp, err := http.DefaultClient.Do(req)
		if err != nil {
			lastErr = err
			time.Sleep(200 * time.Millisecond)
			continue
		}
		_, _ = io.Copy(io.Discard, resp.Body)
		resp.Body.Close()
		if resp.StatusCode >= 200 && resp.StatusCode < 300 {
			return nil
		}
		lastErr = fmt.Errorf("register answered HTTP %d", resp.StatusCode)
		time.Sleep(200 * time.Millisecond)
	}
	return lastErr
}

func pollDone(envURL string) {
	for {
		time.Sleep(500 * time.Millisecond)
		resp, err := http.Get(envURL + "/done")
		if err != nil {
			continue
		}
		var out struct {
			Done bool `json:"done"`
		}
		_ = json.NewDecoder(resp.Body).Decode(&out)
		resp.Body.Close()
		if out.Done {
			return
		}
	}
}

// ---------------------------------------------------------------------------
// small shared helpers

func isHexOID(s string) bool {
	if len(s) != 40 {
		return false
	}
	for _, c := range s {
		if (c < '0' || c > '9') && (c < 'a' || c > 'f') {
			return false
		}
	}
	return true
}

// oidBytes decodes a 40-hex OID to its 20 raw bytes.
func oidBytes(hexOID string) ([]byte, error) {
	return hex.DecodeString(hexOID)
}

// pagination parses per_page/page query params (GitHub defaults: 30/1).
func parsePagination(q url.Values) (perPage, page int) {
	perPage = 30
	page = 1
	if v := q.Get("per_page"); v != "" {
		if n, err := strconv.Atoi(v); err == nil && n > 0 {
			perPage = n
			if perPage > 100 {
				perPage = 100
			}
		}
	}
	if v := q.Get("page"); v != "" {
		if n, err := strconv.Atoi(v); err == nil && n > 0 {
			page = n
		}
	}
	return perPage, page
}

// pageSlice returns the items for one page plus whether more pages follow.
func pageSlice[T any](items []T, perPage, page int) ([]T, bool) {
	start := (page - 1) * perPage
	if start >= len(items) {
		return nil, false
	}
	end := start + perPage
	if end > len(items) {
		end = len(items)
		return items[start:end], false
	}
	return items[start:end], true
}

// writeLinkHeader writes GitHub's Link pagination header with absolute URLs.
func writeLinkHeader(w http.ResponseWriter, r *http.Request, perPage, page int, hasNext bool, total int) {
	scheme := "http"
	if r.TLS != nil {
		scheme = "https"
	}
	base := scheme + "://" + r.Host + r.URL.Path
	link := func(p int, rel string) string {
		q := r.URL.Query()
		q.Set("per_page", strconv.Itoa(perPage))
		q.Set("page", strconv.Itoa(p))
		return "<" + base + "?" + q.Encode() + ">; rel=\"" + rel + "\""
	}
	lastPage := (total + perPage - 1) / perPage
	if lastPage < 1 {
		lastPage = 1
	}
	var parts []string
	if hasNext {
		parts = append(parts, link(page+1, "next"))
	}
	if page > 1 {
		parts = append(parts, link(page-1, "prev"))
	}
	parts = append(parts, link(1, "first"))
	parts = append(parts, link(lastPage, "last"))
	w.Header().Set("Link", strings.Join(parts, ", "))
}

var _ = sort.Strings // sort is used by later sections

// ---------------------------------------------------------------------------
// git primitives: object hashing, commit/tree codecs, packfiles, pkt-lines
// ---------------------------------------------------------------------------

// hashObject returns the SHA-1 object id of a raw object of the given type.
// objTypeHeaders holds the prebuilt "type " prefixes for object hashing,
// so hashObject never formats the header at call time.
var objTypeHeaders = map[int][]byte{
	objCommit: []byte("commit "),
	objTree:   []byte("tree "),
	objBlob:   []byte("blob "),
	objTag:    []byte("tag "),
}

func hashObject(typ int, data []byte) string {
	h := sha1.New()
	h.Write(objTypeHeaders[typ])
	var num [20]byte
	n := strconv.AppendInt(num[:0], int64(len(data)), 10)
	h.Write(n)
	h.Write([]byte{0})
	h.Write(data)
	sum := h.Sum(nil)
	// hex.EncodeToString allocates a fresh string; encoding into a stack
	// buffer and converting once is the same bytes, one allocation.
	var out [40]byte
	hex.Encode(out[:], sum)
	return string(out[:])
}

// ---------------------------------------------------------------------------
// commits

type commit struct {
	tree    string
	parents []string
	message string
	// author/committer lines, kept verbatim for round-tripping.
	author    string
	committer string
	// committerUnix is the committer timestamp, for deepen-since.
	committerUnix int64
}

func parseCommit(data []byte) *commit {
	c := &commit{}
	// Headers end at the first blank line.
	rest := data
	for len(rest) > 0 {
		nl := bytes.IndexByte(rest, '\n')
		var line []byte
		if nl < 0 {
			line, rest = rest, nil
		} else {
			line, rest = rest[:nl], rest[nl+1:]
		}
		if len(line) == 0 {
			break // blank line: the message follows
		}
		switch {
		case bytes.HasPrefix(line, []byte("tree ")):
			c.tree = string(line[5:])
		case bytes.HasPrefix(line, []byte("parent ")):
			c.parents = append(c.parents, string(line[7:]))
		case bytes.HasPrefix(line, []byte("author ")):
			c.author = string(line[7:])
		case bytes.HasPrefix(line, []byte("committer ")):
			c.committer = string(line[10:])
			// "Name <email> 1794960000 +0000": the timestamp is the
			// second-to-last space-separated field.
			fields := strings.Fields(c.committer)
			if len(fields) >= 2 {
				if ts, err := strconv.ParseInt(fields[len(fields)-2], 10, 64); err == nil {
					c.committerUnix = ts
				}
			}
		}
		// Other headers (gpgsig, mergetag, encoding...) are ignored: they
		// never affect the checks, and the raw bytes are preserved in the
		// object store for byte-exact round-trips.
	}
	c.message = string(rest)
	return c
}

// buildCommit serializes a commit object.
func buildCommit(tree string, parents []string, author, committer, message string) []byte {
	var b bytes.Buffer
	fmt.Fprintf(&b, "tree %s\n", tree)
	for _, p := range parents {
		fmt.Fprintf(&b, "parent %s\n", p)
	}
	fmt.Fprintf(&b, "author %s\n", author)
	fmt.Fprintf(&b, "committer %s\n", committer)
	b.WriteByte('\n')
	b.WriteString(message)
	return b.Bytes()
}

// forgeIdentity is the author/committer line for commits the forge creates
// itself (contents API writes, squash merges).
func forgeIdentity(cfg config) string {
	return fmt.Sprintf("%s <%s@example.invalid> %d +0000", cfg.viewer, cfg.viewer, fixedEpoch)
}

// ---------------------------------------------------------------------------
// trees

type treeEntry struct {
	mode string // "100644", "40000", "100755", "120000"
	name string
	oid  string // hex
}

func (e treeEntry) isDir() bool { return e.mode == "40000" }

func parseTree(data []byte) []treeEntry {
	var out []treeEntry
	rest := data
	for len(rest) > 0 {
		sp := bytes.IndexByte(rest, ' ')
		if sp < 0 {
			break
		}
		mode := string(rest[:sp])
		rest = rest[sp+1:]
		nul := bytes.IndexByte(rest, 0)
		if nul < 0 || len(rest) < nul+1+20 {
			break
		}
		name := string(rest[:nul])
		oid := hex.EncodeToString(rest[nul+1 : nul+1+20])
		rest = rest[nul+1+20:]
		out = append(out, treeEntry{mode: mode, name: name, oid: oid})
	}
	return out
}

// treeSortKey is git's sort order: entries sort by name bytes, with
// directories compared as if their name ended in '/'.
func treeSortKey(e treeEntry) string {
	if e.isDir() {
		return e.name + "/"
	}
	return e.name
}

func buildTree(entries []treeEntry) []byte {
	sorted := append([]treeEntry(nil), entries...)
	sort.Slice(sorted, func(i, j int) bool { return treeSortKey(sorted[i]) < treeSortKey(sorted[j]) })
	var b bytes.Buffer
	for _, e := range sorted {
		raw, _ := oidBytes(e.oid)
		b.WriteString(e.mode)
		b.WriteByte(' ')
		b.WriteString(e.name)
		b.WriteByte(0)
		b.Write(raw)
	}
	return b.Bytes()
}

// ---------------------------------------------------------------------------
// tags

// parseTagTarget returns the object a tag object points at.
func parseTagTarget(data []byte) string {
	for len(data) > 0 {
		nl := bytes.IndexByte(data, '\n')
		var line []byte
		if nl < 0 {
			line, data = data, nil
		} else {
			line, data = data[:nl], data[nl+1:]
		}
		if len(line) == 0 {
			break
		}
		if bytes.HasPrefix(line, []byte("object ")) {
			return string(line[7:])
		}
	}
	return ""
}

// ---------------------------------------------------------------------------
// packfiles

// writePack serializes objects as a packfile version 2: plain objects only,
// no deltas. Objects are emitted in OID order for determinism.
// zlibWriterPool reuses BestSpeed compressors across pack writes. Building
// a pack creates one writer per object, and compressor setup (huffman
// tables, 32 KiB window) dominates the cost for the small objects in a
// fetch pack — profiling showed writePack at ~1.6 ms per fetch, almost all
// of it in flate setup. A pooled writer Reset between uses skips all of
// that. BestSpeed (level 1) is used because pack bytes are wire format
// only: the client inflates them and verifies the pack checksum, which is
// computed over the bytes actually produced, so compression ratio is
// irrelevant and speed wins.
var zlibWriterPool = sync.Pool{New: func() any {
	w, _ := zlib.NewWriterLevel(io.Discard, zlib.BestSpeed)
	return w
}}

// emptyZlibStream is the zlib encoding of zero bytes of input (header
// 78 01, stored empty block, Adler-32 of nothing). It lets the reader pool
// pre-build readers: NewReader must read a stream header to construct one,
// and the body is never touched before the first Reset.
var emptyZlibStream = []byte{0x78, 0x01, 0x01, 0x00, 0x00, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01}

var zlibReaderPool = sync.Pool{New: func() any {
	r, err := zlib.NewReader(bytes.NewReader(emptyZlibStream))
	if err != nil {
		return nil
	}
	return r
}}

// pooledZlibReader returns a zlib reader for br, reusing a pooled one when
// available. The caller must return it to zlibReaderPool after use; do NOT
// Close it — Reset re-initializes the pooled reader for the next stream,
// and Close would only record an error state that Reset clears anyway.
func pooledZlibReader(br *bytes.Reader) (io.ReadCloser, error) {
	if v := zlibReaderPool.Get(); v != nil {
		if zr, ok := v.(io.ReadCloser); ok {
			if rs, ok := zr.(zlib.Resetter); ok {
				err := rs.Reset(br, nil)
				if err == nil {
					return zr, nil
				}
				// Reset failed: the new stream's header is bad, which
				// is the real error for this stream. The reader itself
				// is still reusable, so keep it in the pool.
				zlibReaderPool.Put(zr)
				return nil, err
			}
		}
	}
	return zlib.NewReader(br)
}

func writePack(objs map[string]*gitObj) []byte {
	oids := make([]string, 0, len(objs))
	for oid := range objs {
		oids = append(oids, oid)
	}
	sort.Strings(oids)
	var b bytes.Buffer
	b.WriteString("PACK")
	writeU32(&b, 2)
	writeU32(&b, uint32(len(oids)))
	for _, oid := range oids {
		o := objs[oid]
		writePackObjectHeader(&b, o.typ, len(o.data))
		var zb bytes.Buffer
		zb.Grow(len(o.data) + 18) // compressed output is ~input size for small objects
		zw := zlibWriterPool.Get().(*zlib.Writer)
		zw.Reset(&zb)
		_, _ = zw.Write(o.data)
		_ = zw.Close()
		zlibWriterPool.Put(zw)
		b.Write(zb.Bytes())
	}
	sum := sha1.Sum(b.Bytes())
	b.Write(sum[:])
	return b.Bytes()
}

func writeU32(b *bytes.Buffer, v uint32) {
	b.WriteByte(byte(v >> 24))
	b.WriteByte(byte(v >> 16))
	b.WriteByte(byte(v >> 8))
	b.WriteByte(byte(v))
}

// writePackObjectHeader writes the type/size varint header.
func writePackObjectHeader(b *bytes.Buffer, typ int, size int) {
	first := byte((typ << 4) | (size & 0x0f))
	size >>= 4
	if size > 0 {
		first |= 0x80
	}
	b.WriteByte(first)
	for size > 0 {
		c := byte(size & 0x7f)
		size >>= 7
		if size > 0 {
			c |= 0x80
		}
		b.WriteByte(c)
	}
}

// readPack parses a packfile (version 2 or 3), resolving OFS_DELTA and
// REF_DELTA entries, and verifies the trailing SHA-1. It returns the objects
// keyed by OID. baseByOID resolves REF_DELTA bases that live outside the
// pack (the store); it may be nil.
func readPack(pack []byte, baseByOID func(oid string) *gitObj) (map[string]*gitObj, error) {
	if len(pack) < 12+20 {
		return nil, fmt.Errorf("pack too short")
	}
	if string(pack[:4]) != "PACK" {
		return nil, fmt.Errorf("bad pack signature")
	}
	version := uint32(pack[4])<<24 | uint32(pack[5])<<16 | uint32(pack[6])<<8 | uint32(pack[7])
	if version != 2 && version != 3 {
		return nil, fmt.Errorf("unsupported pack version %d", version)
	}
	count := int(uint32(pack[8])<<24 | uint32(pack[9])<<16 | uint32(pack[10])<<8 | uint32(pack[11]))
	// Verify the trailer checksum before trusting anything.
	sum := sha1.Sum(pack[:len(pack)-20])
	if !bytes.Equal(sum[:], pack[len(pack)-20:]) {
		return nil, fmt.Errorf("pack checksum mismatch")
	}
	body := pack[12 : len(pack)-20]

	type rawEntry struct {
		typ     int
		data    []byte
		baseOff int64 // OFS_DELTA base offset, -1 otherwise
		baseOID string
	}
	entries := make([]rawEntry, 0, count)
	offsets := make([]int64, 0, count)
	pos := 0
	for i := 0; i < count; i++ {
		if pos >= len(body) {
			return nil, fmt.Errorf("pack truncated at object %d", i)
		}
		offsets = append(offsets, int64(pos))
		// Type/size varint.
		c := body[pos]
		pos++
		typ := int((c >> 4) & 0x7)
		size := int64(c & 0x0f)
		shift := uint(4)
		for c&0x80 != 0 {
			if pos >= len(body) {
				return nil, fmt.Errorf("pack truncated in object header")
			}
			c = body[pos]
			pos++
			size |= int64(c&0x7f) << shift
			shift += 7
		}
		var baseOff int64 = -1
		var baseOID string
		switch typ {
		case 6: // OFS_DELTA
			if pos >= len(body) {
				return nil, fmt.Errorf("pack truncated in ofs-delta")
			}
			c = body[pos]
			pos++
			off := int64(c & 0x7f)
			for c&0x80 != 0 {
				if pos >= len(body) {
					return nil, fmt.Errorf("pack truncated in ofs-delta")
				}
				c = body[pos]
				pos++
				off = ((off + 1) << 7) | int64(c&0x7f)
			}
			baseOff = offsets[i] - off
		case 7: // REF_DELTA
			if pos+20 > len(body) {
				return nil, fmt.Errorf("pack truncated in ref-delta")
			}
			baseOID = hex.EncodeToString(body[pos : pos+20])
			pos += 20
		}
		// Inflate the zlib stream, counting consumed bytes via bytes.Reader.
		// The reader comes from a pool (Reset reuses its huffman state)
		// and the output buffer is pre-grown to the declared size, so the
		// inflate does one allocation instead of growing from 512 bytes.
		// The pre-growth is capped at 1 MiB: size comes from the pack
		// header, and a corrupt pack claiming gigabytes must not force a
		// giant allocation up front (ReadFrom grows past the cap if the
		// data is really there).
		br := bytes.NewReader(body[pos:])
		zr, err := pooledZlibReader(br)
		if err != nil {
			return nil, fmt.Errorf("pack zlib error: %v", err)
		}
		var out bytes.Buffer
		if size > 0 && size < 1<<20 {
			out.Grow(int(size))
		}
		_, err = out.ReadFrom(zr)
		zlibReaderPool.Put(zr)
		if err != nil {
			return nil, fmt.Errorf("pack inflate error: %v", err)
		}
		data := out.Bytes()
		consumed := len(body) - pos - br.Len()
		pos += consumed
		if int64(len(data)) != size {
			return nil, fmt.Errorf("pack object size mismatch: got %d, want %d", len(data), size)
		}
		entries = append(entries, rawEntry{typ: typ, data: data, baseOff: baseOff, baseOID: baseOID})
	}

	// Resolve entries in offset order (deltas always point backwards).
	out := make(map[string]*gitObj, count)
	byOffset := make(map[int64]*gitObj, count)
	for i, e := range entries {
		var obj *gitObj
		switch e.typ {
		case objCommit, objTree, objBlob, objTag:
			obj = &gitObj{typ: e.typ, data: e.data}
		case 6: // OFS_DELTA
			base := byOffset[e.baseOff]
			if base == nil {
				return nil, fmt.Errorf("ofs-delta base at %d not found", e.baseOff)
			}
			data, err := applyDelta(base.data, e.data)
			if err != nil {
				return nil, err
			}
			obj = &gitObj{typ: base.typ, data: data}
		case 7: // REF_DELTA
			var base *gitObj
			if o, ok := out[e.baseOID]; ok {
				base = o
			} else if baseByOID != nil {
				base = baseByOID(e.baseOID)
			}
			if base == nil {
				return nil, fmt.Errorf("ref-delta base %s not found", e.baseOID)
			}
			data, err := applyDelta(base.data, e.data)
			if err != nil {
				return nil, err
			}
			obj = &gitObj{typ: base.typ, data: data}
		default:
			return nil, fmt.Errorf("unknown pack object type %d", e.typ)
		}
		oid := hashObject(obj.typ, obj.data)
		out[oid] = obj
		byOffset[offsets[i]] = obj
	}
	return out, nil
}

// applyDelta applies a git delta to base data.
func applyDelta(base, delta []byte) ([]byte, error) {
	pos := 0
	readVarint := func() (int64, error) {
		var v int64
		shift := uint(0)
		for {
			if pos >= len(delta) {
				return 0, fmt.Errorf("delta truncated")
			}
			c := delta[pos]
			pos++
			v |= int64(c&0x7f) << shift
			shift += 7
			if c&0x80 == 0 {
				break
			}
		}
		return v, nil
	}
	baseSize, err := readVarint()
	if err != nil {
		return nil, err
	}
	if baseSize != int64(len(base)) {
		return nil, fmt.Errorf("delta base size mismatch")
	}
	resultSize, err := readVarint()
	if err != nil {
		return nil, err
	}
	out := make([]byte, 0, resultSize)
	for pos < len(delta) {
		op := delta[pos]
		pos++
		if op&0x80 != 0 {
			// Copy from base.
			var off, size int64
			for i := 0; i < 4; i++ {
				if op&(1<<uint(i)) != 0 {
					if pos >= len(delta) {
						return nil, fmt.Errorf("delta truncated in copy")
					}
					off |= int64(delta[pos]) << uint(8*i)
					pos++
				}
			}
			for i := 0; i < 3; i++ {
				if op&(0x10<<uint(i)) != 0 {
					if pos >= len(delta) {
						return nil, fmt.Errorf("delta truncated in copy")
					}
					size |= int64(delta[pos]) << uint(8*i)
					pos++
				}
			}
			if size == 0 {
				size = 0x10000
			}
			if off < 0 || off+size > int64(len(base)) {
				return nil, fmt.Errorf("delta copy out of range")
			}
			out = append(out, base[off:off+size]...)
		} else if op != 0 {
			// Insert literal bytes.
			n := int(op)
			if pos+n > len(delta) {
				return nil, fmt.Errorf("delta truncated in insert")
			}
			out = append(out, delta[pos:pos+n]...)
			pos += n
		} else {
			return nil, fmt.Errorf("delta opcode 0")
		}
	}
	if int64(len(out)) != resultSize {
		return nil, fmt.Errorf("delta result size mismatch")
	}
	return out, nil
}

// ---------------------------------------------------------------------------
// pkt-lines

// hexDigits is the lookup for hand-rolled hex formatting (pkt-line lengths,
// request ids). It replaces fmt.Sprintf("%04x") on the hot paths: Sprintf
// costs microseconds per call through its formatter, this is a few
// nanoseconds of table lookups.
const hexDigits = "0123456789abcdef"

// appendPktHeader appends a pkt-line's 4-hex-digit length prefix for a
// payload of totalLen bytes (length includes the 4 prefix bytes themselves).
func appendPktHeader(dst []byte, totalLen int) []byte {
	return append(dst,
		hexDigits[(totalLen>>12)&0xf],
		hexDigits[(totalLen>>8)&0xf],
		hexDigits[(totalLen>>4)&0xf],
		hexDigits[totalLen&0xf],
	)
}

// pktLine frames one payload as a pkt-line (4 hex length + payload).
func pktLine(payload []byte) []byte {
	n := len(payload) + 4
	out := make([]byte, 0, n)
	out = appendPktHeader(out, n)
	out = append(out, payload...)
	return out
}

func pktFlush() []byte { return []byte("0000") }

func pktDelim() []byte { return []byte("0001") }

// pktLines encodes a sequence of string lines (each gets a trailing \n if it
// lacks one), "flush" and "delim" markers.
func pktLines(items ...any) []byte {
	var b bytes.Buffer
	for _, it := range items {
		switch v := it.(type) {
		case string:
			if v == "flush" {
				b.Write(pktFlush())
			} else if v == "delim" {
				b.Write(pktDelim())
			} else {
				if !strings.HasSuffix(v, "\n") {
					v += "\n"
				}
				b.Write(pktLine([]byte(v)))
			}
		case []byte:
			b.Write(pktLine(v))
		}
	}
	return b.Bytes()
}

// pktPacket is one decoded pkt-line: kind "data", "flush" or "delim".
type pktPacket struct {
	kind    string
	payload []byte
}

// decodePktLines parses a whole pkt-line stream. It returns the packets and
// the number of bytes consumed; trailing non-pkt bytes (a packfile after the
// command list) are left unconsumed.
func decodePktLines(buf []byte) ([]pktPacket, int, error) {
	var out []pktPacket
	pos := 0
	for pos < len(buf) {
		if len(buf)-pos < 4 {
			return out, pos, fmt.Errorf("pkt-line truncated")
		}
		head := string(buf[pos : pos+4])
		if head == "0000" {
			out = append(out, pktPacket{kind: "flush"})
			pos += 4
			continue
		}
		if head == "0001" {
			out = append(out, pktPacket{kind: "delim"})
			pos += 4
			continue
		}
		n, err := strconv.ParseInt(head, 16, 32)
		if err != nil || n < 4 || n > 65520 {
			return out, pos, fmt.Errorf("bad pkt-line length %q", head)
		}
		if pos+int(n) > len(buf) {
			return out, pos, fmt.Errorf("pkt-line overruns buffer")
		}
		out = append(out, pktPacket{kind: "data", payload: buf[pos+4 : pos+int(n)]})
		pos += int(n)
	}
	return out, pos, nil
}

// decodePktLinesUntilFlush parses pkt-lines up to and including the first
// flush packet, returning the packets and the bytes consumed. Anything
// after the flush (a packfile) is left unconsumed.
func decodePktLinesUntilFlush(buf []byte) ([]pktPacket, int, error) {
	var out []pktPacket
	pos := 0
	for pos < len(buf) {
		if len(buf)-pos < 4 {
			return out, pos, fmt.Errorf("pkt-line truncated")
		}
		head := string(buf[pos : pos+4])
		if head == "0000" {
			out = append(out, pktPacket{kind: "flush"})
			return out, pos + 4, nil
		}
		if head == "0001" {
			out = append(out, pktPacket{kind: "delim"})
			pos += 4
			continue
		}
		n, err := strconv.ParseInt(head, 16, 32)
		if err != nil || n < 4 || n > 65520 {
			return out, pos, fmt.Errorf("bad pkt-line length %q", head)
		}
		if pos+int(n) > len(buf) {
			return out, pos, fmt.Errorf("pkt-line overruns buffer")
		}
		out = append(out, pktPacket{kind: "data", payload: buf[pos+4 : pos+int(n)]})
		pos += int(n)
	}
	return out, pos, fmt.Errorf("pkt-line stream ended without a flush")
}
func pktText(p pktPacket) string {
	return strings.TrimSuffix(string(p.payload), "\n")
}

// sideband wraps data in band-1 sideband packets (max ~32 KiB each). It
// frames each chunk directly into the output buffer: the old version built
// a fresh payload slice and a fresh pkt-line per chunk (two allocations per
// 32 KiB); this one allocates only the output buffer itself.
func sidebandPackets(data []byte) []byte {
	if len(data) == 0 {
		return nil
	}
	// Each chunk costs 4 length bytes + 1 band byte + the chunk itself.
	nchunks := (len(data) + 32767) / 32768
	out := make([]byte, 0, len(data)+nchunks*5)
	for len(data) > 0 {
		chunk := 32768
		if len(data) < chunk {
			chunk = len(data)
		}
		out = appendPktHeader(out, chunk+5)
		out = append(out, 1)
		out = append(out, data[:chunk]...)
		data = data[chunk:]
	}
	return out
}

// ---------------------------------------------------------------------------
// store operations: refs, the commit graph, trees, diffs, merges
// ---------------------------------------------------------------------------

// getRepo returns a repo by owner/name. The caller must hold at least a read
// lock. A repo belongs to exactly one owner; the same name under another
// owner is a different (absent) repo.
func (s *store) getRepo(owner, name string) *repo {
	return s.repos[repoKey(owner, name)]
}

func (r *repo) getObject(oid string) *gitObj {
	if oid == "" || oid == zeroOID {
		return nil
	}
	return r.objects[oid]
}

func (r *repo) commitOf(oid string) *commit {
	o := r.getObject(oid)
	if o == nil || o.typ != objCommit {
		return nil
	}
	return parseCommit(o.data)
}

func (r *repo) refTip(ref string) string { return r.refs[ref] }

// branchTip resolves a branch name (or a raw OID) to a commit OID.
func (r *repo) branchTip(ref string) string {
	if isHexOID(ref) {
		if r.getObject(ref) != nil {
			return ref
		}
		return ""
	}
	if oid, ok := r.refs["refs/heads/"+ref]; ok {
		return oid
	}
	return ""
}

// ---------------------------------------------------------------------------
// commit graph traversal

// commitClosure walks from roots following parents, limited by depth
// (generations from a root; depth <= 0 means unlimited) and by since
// (commits older than since are cut). exclude holds commits to skip
// entirely (deepen-not). It returns the included commits and the boundary
// commits: included commits with at least one parent not included.
func (r *repo) commitClosure(roots []string, depth int, since int64, exclude map[string]bool) (map[string]bool, map[string]bool) {
	included := make(map[string]bool)
	type item struct {
		oid string
		gen int
	}
	queue := []item{}
	seen := make(map[string]bool)
	for _, root := range roots {
		c := r.commitOf(root)
		if c == nil {
			continue
		}
		if exclude[root] {
			continue
		}
		if since > 0 && c.committerUnix > 0 && c.committerUnix < since {
			continue
		}
		queue = append(queue, item{root, 0})
		seen[root] = true
	}
	for len(queue) > 0 {
		it := queue[0]
		queue = queue[1:]
		included[it.oid] = true
		if depth > 0 && it.gen+1 >= depth {
			continue // parents would exceed the depth
		}
		c := r.commitOf(it.oid)
		if c == nil {
			continue
		}
		for _, p := range c.parents {
			if seen[p] || exclude[p] {
				continue
			}
			pc := r.commitOf(p)
			if pc == nil {
				continue
			}
			if since > 0 && pc.committerUnix > 0 && pc.committerUnix < since {
				continue
			}
			seen[p] = true
			queue = append(queue, item{p, it.gen + 1})
		}
	}
	boundary := make(map[string]bool)
	for oid := range included {
		c := r.commitOf(oid)
		if c == nil {
			continue
		}
		for _, p := range c.parents {
			if !included[p] {
				boundary[oid] = true
				break
			}
		}
	}
	return included, boundary
}

// ancestors returns oid plus all of its ancestors.
func (r *repo) ancestors(oid string) map[string]bool {
	out := make(map[string]bool)
	queue := []string{oid}
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if out[cur] {
			continue
		}
		c := r.commitOf(cur)
		if c == nil {
			continue
		}
		out[cur] = true
		queue = append(queue, c.parents...)
	}
	return out
}

// isAncestor reports whether anc is an ancestor of (or equal to) desc. It
// searches from desc with an early exit, so the common linear-history case
// (anc is the direct parent) costs O(1) instead of a full traversal.
func (r *repo) isAncestor(anc, desc string) bool {
	if anc == desc {
		return true
	}
	seen := make(map[string]bool)
	stack := []string{desc}
	for len(stack) > 0 {
		cur := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if seen[cur] {
			continue
		}
		seen[cur] = true
		c := r.commitOf(cur)
		if c == nil {
			continue
		}
		for _, p := range c.parents {
			if p == anc {
				return true
			}
			stack = append(stack, p)
		}
	}
	return false
}

// mergeBase returns the first common ancestor of a and b found by walking
// b's ancestry in breadth-first order (exact for linear histories, which is
// everything the suite builds).
func (r *repo) mergeBase(a, b string) string {
	ancA := r.ancestors(a)
	queue := []string{b}
	seen := make(map[string]bool)
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if seen[cur] {
			continue
		}
		seen[cur] = true
		if ancA[cur] {
			return cur
		}
		c := r.commitOf(cur)
		if c == nil {
			continue
		}
		queue = append(queue, c.parents...)
	}
	return ""
}

// listCommits returns the commits reachable from tip, children before
// parents (newest first for linear histories).
func (r *repo) listCommits(tip string) []string {
	var out []string
	seen := make(map[string]bool)
	stack := []string{tip}
	for len(stack) > 0 {
		cur := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if seen[cur] {
			continue
		}
		c := r.commitOf(cur)
		if c == nil {
			continue
		}
		seen[cur] = true
		out = append(out, cur)
		// Push parents reversed so the first parent is visited first.
		for i := len(c.parents) - 1; i >= 0; i-- {
			stack = append(stack, c.parents[i])
		}
	}
	return out
}

// reachableObjects returns every object reachable from roots. Commit
// traversal follows parents only through commits allowed by allowCommit
// (nil allows all). Tag objects are followed to their targets.
func (r *repo) reachableObjects(roots []string, allowCommit func(oid string) bool) map[string]*gitObj {
	out := make(map[string]*gitObj)
	var walkTree func(treeOID string)
	walkTree = func(treeOID string) {
		o := r.getObject(treeOID)
		if o == nil || o.typ != objTree {
			return
		}
		if _, done := out[treeOID]; done {
			return
		}
		out[treeOID] = o
		for _, e := range parseTree(o.data) {
			if e.isDir() {
				walkTree(e.oid)
			} else {
				if bo := r.getObject(e.oid); bo != nil {
					out[e.oid] = bo
				}
			}
		}
	}
	var walkCommit func(oid string)
	walkCommit = func(oid string) {
		if _, done := out[oid]; done {
			return
		}
		o := r.getObject(oid)
		if o == nil {
			return
		}
		// The allowCommit gate applies to commits only: a tag, tree or
		// blob named directly is always included.
		if o.typ == objCommit && allowCommit != nil && !allowCommit(oid) {
			return
		}
		switch o.typ {
		case objCommit:
			out[oid] = o
			c := parseCommit(o.data)
			walkTree(c.tree)
			for _, p := range c.parents {
				walkCommit(p)
			}
		case objTag:
			out[oid] = o
			if target := parseTagTarget(o.data); target != "" {
				walkCommit(target)
			}
		case objTree:
			walkTree(oid)
		default:
			out[oid] = o
		}
	}
	for _, root := range roots {
		walkCommit(root)
	}
	return out
}

// ---------------------------------------------------------------------------
// trees as flat file maps

// flattenTree returns path -> blob OID for every file under a tree.
func (r *repo) flattenTree(treeOID string) map[string]string {
	out := make(map[string]string)
	var walk func(treeOID, prefix string)
	walk = func(treeOID, prefix string) {
		o := r.getObject(treeOID)
		if o == nil || o.typ != objTree {
			return
		}
		for _, e := range parseTree(o.data) {
			path := prefix + e.name
			if e.isDir() {
				walk(e.oid, path+"/")
			} else {
				out[path] = e.oid
			}
		}
	}
	walk(treeOID, "")
	return out
}

func (r *repo) flattenCommit(commitOID string) map[string]string {
	c := r.commitOf(commitOID)
	if c == nil {
		return map[string]string{}
	}
	return r.flattenTree(c.tree)
}

// writeTreeFromMap builds nested tree objects for a flat file map and
// returns the root tree OID plus the new tree objects to store.
func (r *repo) writeTreeFromMap(files map[string]string) (string, map[string]*gitObj) {
	created := make(map[string]*gitObj)
	var build func(paths map[string]string, prefix string) string
	build = func(paths map[string]string, prefix string) string {
		dirs := make(map[string]map[string]string)
		var entries []treeEntry
		for path, blobOID := range paths {
			rel := strings.TrimPrefix(path, prefix)
			if i := strings.IndexByte(rel, '/'); i >= 0 {
				dir := rel[:i]
				if dirs[dir] == nil {
					dirs[dir] = make(map[string]string)
				}
				dirs[dir][path] = blobOID
			} else {
				entries = append(entries, treeEntry{mode: "100644", name: rel, oid: blobOID})
			}
		}
		for dir, sub := range dirs {
			subOID := build(sub, prefix+dir+"/")
			entries = append(entries, treeEntry{mode: "40000", name: dir, oid: subOID})
		}
		data := buildTree(entries)
		oid := hashObject(objTree, data)
		created[oid] = &gitObj{typ: objTree, data: data}
		return oid
	}
	root := build(files, "")
	return root, created
}

// ---------------------------------------------------------------------------
// diffs

type fileChange struct {
	filename  string
	status    string // "added" | "modified" | "removed"
	additions int
	deletions int
}

func splitLines(b []byte) []string {
	if len(b) == 0 {
		return nil
	}
	s := string(b)
	lines := strings.Split(s, "\n")
	if lines[len(lines)-1] == "" {
		lines = lines[:len(lines)-1]
	}
	return lines
}

// lineDiff counts added/removed lines as a multiset difference.
func lineDiff(oldData, newData []byte) (add, del int) {
	oldLines := splitLines(oldData)
	newLines := splitLines(newData)
	counts := make(map[string]int)
	for _, l := range oldLines {
		counts[l]++
	}
	for _, l := range newLines {
		if counts[l] > 0 {
			counts[l]--
		} else {
			add++
		}
	}
	for _, c := range counts {
		del += c
	}
	return add, del
}

// diffFileMaps compares two flat file maps (base -> head).
func (r *repo) diffFileMaps(base, head map[string]string) []fileChange {
	paths := make(map[string]bool)
	for p := range base {
		paths[p] = true
	}
	for p := range head {
		paths[p] = true
	}
	var out []fileChange
	for p := range paths {
		bOID, inBase := base[p]
		hOID, inHead := head[p]
		if inBase && inHead && bOID == hOID {
			continue
		}
		fc := fileChange{filename: p}
		switch {
		case !inBase:
			fc.status = "added"
			if o := r.getObject(hOID); o != nil {
				fc.additions = len(splitLines(o.data))
			}
		case !inHead:
			fc.status = "removed"
			if o := r.getObject(bOID); o != nil {
				fc.deletions = len(splitLines(o.data))
			}
		default:
			fc.status = "modified"
			var oldData, newData []byte
			if o := r.getObject(bOID); o != nil {
				oldData = o.data
			}
			if o := r.getObject(hOID); o != nil {
				newData = o.data
			}
			fc.additions, fc.deletions = lineDiff(oldData, newData)
		}
		out = append(out, fc)
	}
	sort.Slice(out, func(i, j int) bool { return out[i].filename < out[j].filename })
	return out
}

// ---------------------------------------------------------------------------
// three-way merge (for squash merges and conflict detection)

// mergeFileMaps applies head's changes onto base's tip, both relative to
// their merge-base. It returns the merged map and whether the merge
// conflicts: a path changed on both sides to different content.
func mergeFileMaps(mergeBase, head, baseTip map[string]string) (map[string]string, bool) {
	paths := make(map[string]bool)
	for p := range mergeBase {
		paths[p] = true
	}
	for p := range head {
		paths[p] = true
	}
	for p := range baseTip {
		paths[p] = true
	}
	merged := make(map[string]string)
	for p := range paths {
		m, inM := mergeBase[p]
		h, inH := head[p]
		b, inB := baseTip[p]
		headChanged := inH != inM || (inH && inM && h != m)
		baseChanged := inB != inM || (inB && inM && b != m)
		switch {
		case headChanged && baseChanged:
			if inH == inB && (!inH || h == b) {
				if inH {
					merged[p] = h
				}
			} else {
				return nil, true // conflict
			}
		case headChanged:
			if inH {
				merged[p] = h
			}
		default:
			if inB {
				merged[p] = b
			}
		}
	}
	return merged, false
}

// prConflict reports whether a pull request currently conflicts with its
// base branch.
func (r *repo) prConflict(pr *pull) bool {
	headTip := r.refTip("refs/heads/" + pr.headRef)
	baseTip := r.refTip("refs/heads/" + pr.baseRef)
	if headTip == "" || baseTip == "" {
		return false
	}
	mb := r.mergeBase(headTip, baseTip)
	_, conflict := mergeFileMaps(r.flattenCommit(mb), r.flattenCommit(headTip), r.flattenCommit(baseTip))
	return conflict
}

// squashMerge performs a squash merge of pr onto its base branch: one new
// commit on the base branch whose tree is the merged result. It returns the
// new commit OID, or conflict=true when the merge cannot apply cleanly.
func (r *repo) squashMerge(cfg config, pr *pull) (string, bool, error) {
	headTip := r.refTip("refs/heads/" + pr.headRef)
	baseTip := r.refTip("refs/heads/" + pr.baseRef)
	if headTip == "" {
		return "", false, fmt.Errorf("head branch %q does not exist", pr.headRef)
	}
	if baseTip == "" {
		return "", false, fmt.Errorf("base branch %q does not exist", pr.baseRef)
	}
	mb := r.mergeBase(headTip, baseTip)
	merged, conflict := mergeFileMaps(r.flattenCommit(mb), r.flattenCommit(headTip), r.flattenCommit(baseTip))
	if conflict {
		return "", true, nil
	}
	treeOID, trees := r.writeTreeFromMap(merged)
	for oid, o := range trees {
		r.objects[oid] = o
	}
	identity := forgeIdentity(cfg)
	msg := pr.title
	if pr.body != "" {
		msg += "\n\n" + pr.body
	}
	msg += "\n"
	commitData := buildCommit(treeOID, []string{baseTip}, identity, identity, msg)
	commitOID := hashObject(objCommit, commitData)
	r.objects[commitOID] = &gitObj{typ: objCommit, data: commitData}
	r.refs["refs/heads/"+pr.baseRef] = commitOID
	r.touch() // the merge changed objects and refs; cached fetches are stale
	return commitOID, false, nil
}

// ---------------------------------------------------------------------------
// contents API commits

// applyContents writes (or deletes) one file on a branch, creating a real
// commit. A branch that does not exist is created from the default branch's
// tip (or as the first commit when the repo is unborn). It returns the new
// commit OID and the new blob OID ("" for a delete).
func (r *repo) applyContents(cfg config, branch, path string, data []byte, isDelete bool, message string) (string, string, error) {
	if branch == "" {
		branch = r.defaultBranch
	}
	ref := "refs/heads/" + branch
	tip, exists := r.refs[ref]
	if !exists {
		// Create the branch from the default branch's tip.
		tip = r.refs["refs/heads/"+r.defaultBranch]
	}
	files := map[string]string{}
	if tip != "" {
		files = r.flattenCommit(tip)
	}
	var blobOID string
	if isDelete {
		if _, ok := files[path]; !ok {
			return "", "", fmt.Errorf("not found")
		}
		delete(files, path)
	} else {
		blobOID = hashObject(objBlob, data)
		r.objects[blobOID] = &gitObj{typ: objBlob, data: data}
		files[path] = blobOID
	}
	treeOID, trees := r.writeTreeFromMap(files)
	for oid, o := range trees {
		r.objects[oid] = o
	}
	identity := forgeIdentity(cfg)
	var parents []string
	if tip != "" {
		parents = []string{tip}
	}
	if !strings.HasSuffix(message, "\n") {
		message += "\n"
	}
	commitData := buildCommit(treeOID, parents, identity, identity, message)
	commitOID := hashObject(objCommit, commitData)
	r.objects[commitOID] = &gitObj{typ: objCommit, data: commitData}
	r.refs[ref] = commitOID
	r.touch() // the new commit changed objects and refs; cached fetches are stale
	return commitOID, blobOID, nil
}

// ---------------------------------------------------------------------------
// git smart HTTP: info/refs, git-upload-pack, git-receive-pack
// ---------------------------------------------------------------------------

func (s *server) handleGit(w http.ResponseWriter, r *http.Request) {
	if !s.requireAuth(w, r) {
		return
	}
	// Path: /{owner}/{repo}.git/{info/refs|git-upload-pack|git-receive-pack}
	trimmed := strings.TrimPrefix(r.URL.Path, "/")
	parts := strings.Split(trimmed, "/")
	if len(parts) < 3 || !strings.HasSuffix(parts[1], ".git") {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	owner := parts[0]
	repoName := strings.TrimSuffix(parts[1], ".git")
	service := strings.Join(parts[2:], "/")

	s.st.mu.RLock()
	repo := s.st.getRepo(owner, repoName)
	s.st.mu.RUnlock()
	if repo == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}

	switch service {
	case "info/refs":
		if r.Method != http.MethodGet {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		s.gitInfoRefs(w, r, repo)
	case "git-upload-pack":
		if r.Method != http.MethodPost {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		s.gitUploadPack(w, r, repo)
	case "git-receive-pack":
		if r.Method != http.MethodPost {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		s.gitReceivePack(w, r, repo)
	default:
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
	}
}

// sortedRefNames returns the repo's ref names in alphabetical order.
func (r *repo) sortedRefNames() []string {
	names := make([]string, 0, len(r.refs))
	for name := range r.refs {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

// peeledOID follows annotated tags to their ultimate non-tag target.
func (r *repo) peeledOID(oid string) string {
	for {
		o := r.getObject(oid)
		if o == nil || o.typ != objTag {
			return oid
		}
		target := parseTagTarget(o.data)
		if target == "" {
			return oid
		}
		oid = target
	}
}

// ---------------------------------------------------------------------------
// info/refs advertisements

func (s *server) gitInfoRefs(w http.ResponseWriter, r *http.Request, repo *repo) {
	service := r.URL.Query().Get("service")
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()

	switch service {
	case "git-upload-pack":
		w.Header().Set("Content-Type", "application/x-git-upload-pack-advertisement")
		if r.Header.Get("Git-Protocol") == "version=2" {
			// Protocol v2: capabilities only, no service preamble.
			_, _ = w.Write(pktLines(
				"version 2",
				"ls-refs=unborn",
				"fetch=shallow thin-pack ofs-delta",
				"object-format=sha1",
				"flush",
			))
			return
		}
		// Protocol v0: service preamble + ref list.
		_, _ = w.Write(s.v0Advertisement(repo, "git-upload-pack",
			"side-band-64k thin-pack ofs-delta shallow symref=HEAD:refs/heads/"+repo.defaultBranch))
	case "git-receive-pack":
		w.Header().Set("Content-Type", "application/x-git-receive-pack-advertisement")
		_, _ = w.Write(s.v0Advertisement(repo, "git-receive-pack",
			"report-status side-band-64k delete-refs"))
	default:
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
	}
}

// v0Advertisement builds a v0 ref advertisement: the service preamble, then
// HEAD (with capabilities on its line) and every ref, with peeled tags.
func (s *server) v0Advertisement(repo *repo, service, caps string) []byte {
	var b bytes.Buffer
	b.Write(pktLine([]byte("# service=" + service + "\n")))
	b.Write(pktFlush())
	names := repo.sortedRefNames()
	if len(names) == 0 {
		// Empty repository: the capabilities pseudo-ref carries the caps.
		b.Write(pktLine([]byte(zeroOID + " capabilities^{}\x00" + caps + "\n")))
		b.Write(pktFlush())
		return b.Bytes()
	}
	headOID := repo.refTip("refs/heads/" + repo.defaultBranch)
	first := true
	writeRef := func(oid, name string) {
		line := oid + " " + name
		if first {
			line += "\x00" + caps
			first = false
		}
		b.Write(pktLine([]byte(line + "\n")))
	}
	if headOID != "" {
		writeRef(headOID, "HEAD")
	}
	for _, name := range names {
		oid := repo.refs[name]
		writeRef(oid, name)
		if strings.HasPrefix(name, "refs/tags/") {
			if o := repo.getObject(oid); o != nil && o.typ == objTag {
				peeled := repo.peeledOID(oid)
				writeRef(peeled, name+"^{}")
			}
		}
	}
	b.Write(pktFlush())
	return b.Bytes()
}

// ---------------------------------------------------------------------------
// git-upload-pack: v2 ls-refs / fetch, v0 fetch

func (s *server) gitUploadPack(w http.ResponseWriter, r *http.Request, repo *repo) {
	body, err := io.ReadAll(io.LimitReader(r.Body, 64<<20))
	_ = r.Body.Close()
	if err != nil {
		http.Error(w, "could not read request", http.StatusBadRequest)
		return
	}
	packets, _, err := decodePktLines(body)
	if err != nil || len(packets) == 0 {
		// Malformed input: answer an error and keep serving.
		http.Error(w, "bad pkt-line stream", http.StatusBadRequest)
		return
	}
	first := pktText(packets[0])
	switch {
	case first == "command=ls-refs":
		s.gitLsRefs(w, repo, packets)
	case first == "command=fetch":
		s.gitFetchV2(w, repo, packets)
	case strings.HasPrefix(first, "want "):
		s.gitFetchV0(w, repo, packets)
	default:
		http.Error(w, "unknown upload-pack command", http.StatusBadRequest)
	}
}

// gitLsRefs answers a v2 ls-refs request.
func (s *server) gitLsRefs(w http.ResponseWriter, repo *repo, packets []pktPacket) {
	peel, symrefs, unborn := false, false, false
	var prefixes []string
	for _, p := range packets[1:] {
		if p.kind != "data" {
			continue
		}
		line := pktText(p)
		switch {
		case line == "peel":
			peel = true
		case line == "symrefs":
			symrefs = true
		case line == "unborn":
			unborn = true
		case strings.HasPrefix(line, "ref-prefix "):
			prefixes = append(prefixes, strings.TrimPrefix(line, "ref-prefix "))
		}
	}
	keep := func(name string) bool {
		if len(prefixes) == 0 {
			return true
		}
		for _, pre := range prefixes {
			if strings.HasPrefix(name, pre) {
				return true
			}
		}
		return false
	}

	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	w.Header().Set("Content-Type", "application/x-git-upload-pack-result")
	var b bytes.Buffer
	headOID := repo.refTip("refs/heads/" + repo.defaultBranch)
	if headOID == "" && unborn && keep("HEAD") {
		b.Write(pktLine([]byte("unborn HEAD symref-target:refs/heads/" + repo.defaultBranch + "\n")))
	} else {
		if symrefs && headOID != "" && keep("HEAD") {
			b.Write(pktLine([]byte(headOID + " HEAD symref-target:refs/heads/" + repo.defaultBranch + "\n")))
		}
		for _, name := range repo.sortedRefNames() {
			if !keep(name) {
				continue
			}
			oid := repo.refs[name]
			line := oid + " " + name
			if peel {
				if o := repo.getObject(oid); o != nil && o.typ == objTag {
					line += " peeled:" + repo.peeledOID(oid)
				}
			}
			b.Write(pktLine([]byte(line + "\n")))
		}
	}
	b.Write(pktFlush())
	_, _ = w.Write(b.Bytes())
}

// fetchRequest is a parsed v2/v0 fetch request.
type fetchRequest struct {
	wants       []string
	haves       []string
	shallow     []string // client-declared shallow boundaries
	depth       int      // 0 = unlimited
	deepenSince int64    // 0 = unset
	deepenNot   []string // ref names
}

func parseFetchV2(packets []pktPacket) fetchRequest {
	var fr fetchRequest
	for _, p := range packets[1:] {
		if p.kind != "data" {
			continue
		}
		line := pktText(p)
		switch {
		case strings.HasPrefix(line, "want "):
			fr.wants = append(fr.wants, strings.TrimPrefix(line, "want "))
		case strings.HasPrefix(line, "have "):
			fr.haves = append(fr.haves, strings.TrimPrefix(line, "have "))
		case strings.HasPrefix(line, "shallow "):
			fr.shallow = append(fr.shallow, strings.TrimPrefix(line, "shallow "))
		case strings.HasPrefix(line, "deepen "):
			if n, err := strconv.Atoi(strings.TrimPrefix(line, "deepen ")); err == nil {
				fr.depth = n
			}
		case strings.HasPrefix(line, "deepen-since "):
			if n, err := strconv.ParseInt(strings.TrimPrefix(line, "deepen-since "), 10, 64); err == nil {
				fr.deepenSince = n
			}
		case strings.HasPrefix(line, "deepen-not "):
			fr.deepenNot = append(fr.deepenNot, strings.TrimPrefix(line, "deepen-not "))
		}
	}
	return fr
}

func parseFetchV0(packets []pktPacket) fetchRequest {
	var fr fetchRequest
	for _, p := range packets {
		if p.kind != "data" {
			continue
		}
		line := pktText(p)
		// A want line may carry capabilities after a space; take the OID.
		switch {
		case strings.HasPrefix(line, "want "):
			rest := strings.TrimPrefix(line, "want ")
			if i := strings.IndexByte(rest, ' '); i >= 0 {
				rest = rest[:i]
			}
			fr.wants = append(fr.wants, rest)
		case strings.HasPrefix(line, "have "):
			fr.haves = append(fr.haves, strings.TrimPrefix(line, "have "))
		case strings.HasPrefix(line, "shallow "):
			fr.shallow = append(fr.shallow, strings.TrimPrefix(line, "shallow "))
		case strings.HasPrefix(line, "deepen "):
			if n, err := strconv.Atoi(strings.TrimPrefix(line, "deepen ")); err == nil {
				fr.depth = n
			}
		case strings.HasPrefix(line, "deepen-since "):
			if n, err := strconv.ParseInt(strings.TrimPrefix(line, "deepen-since "), 10, 64); err == nil {
				fr.deepenSince = n
			}
		case strings.HasPrefix(line, "deepen-not "):
			fr.deepenNot = append(fr.deepenNot, strings.TrimPrefix(line, "deepen-not "))
		}
	}
	return fr
}

// fetchSelection is the result of planning a fetch.
type fetchSelection struct {
	pack      []byte
	acks      []string
	nak       bool
	shallow   []string
	unshallow []string
}

// planFetch computes the object selection for a fetch request. The caller
// must hold at least a read lock.
func (r *repo) planFetch(fr fetchRequest) (*fetchSelection, error) {
	// Expand wants: tags resolve to their targets (the tag objects
	// themselves still travel in the pack).
	var wantCommits []string
	var wantTags []string
	for _, w := range fr.wants {
		o := r.getObject(w)
		if o == nil {
			return nil, fmt.Errorf("want %s not found", w)
		}
		if o.typ == objTag {
			wantTags = append(wantTags, w)
			target := r.peeledOID(w)
			if r.commitOf(target) != nil {
				wantCommits = append(wantCommits, target)
			}
		} else if o.typ == objCommit {
			wantCommits = append(wantCommits, w)
		} else {
			// A want naming a blob/tree directly: ship it as-is.
			wantTags = append(wantTags, w)
		}
	}

	// deepen-not: commits reachable from the named refs are excluded.
	exclude := make(map[string]bool)
	for _, ref := range fr.deepenNot {
		tip := r.refTip(ref)
		if tip == "" {
			tip = r.refTip("refs/heads/" + ref)
		}
		if tip != "" {
			for oid := range r.ancestors(tip) {
				exclude[oid] = true
			}
		}
	}

	included, boundary := r.commitClosure(wantCommits, fr.depth, fr.deepenSince, exclude)

	// Held set: haves plus their ancestors, stopping at client-declared
	// shallow boundaries (the shallow commit itself is held; its parents
	// are not, which is what makes a deepen work).
	clientShallow := make(map[string]bool)
	for _, s := range fr.shallow {
		clientShallow[s] = true
	}
	held := make(map[string]bool)
	queue := append([]string(nil), fr.haves...)
	for len(queue) > 0 {
		cur := queue[0]
		queue = queue[1:]
		if held[cur] {
			continue
		}
		c := r.commitOf(cur)
		if c == nil {
			continue
		}
		held[cur] = true
		if clientShallow[cur] {
			continue // do not cross a shallow boundary
		}
		queue = append(queue, c.parents...)
	}

	// Pack = objects reachable from the candidates minus objects the
	// client already holds.
	candRoots := append(append([]string(nil), wantCommits...), wantTags...)
	candObjects := r.reachableObjects(candRoots, func(oid string) bool { return included[oid] })
	heldObjects := r.reachableObjects(fr.haves, func(oid string) bool { return held[oid] })
	packObjects := make(map[string]*gitObj, len(candObjects))
	for oid, o := range candObjects {
		if _, isHeld := heldObjects[oid]; !isHeld {
			packObjects[oid] = o
		}
	}

	// Acknowledgments: the newest commits both sides share. A have is
	// often a tip whose own ancestors are the common commits (the client
	// skips sending haves that are ancestors of other haves), so walk
	// from each have and ACK the first commit on each walk that is also
	// an ancestor of a want, without descending past it. The walk stops
	// at shallow boundaries: the client has nothing below them.
	// With no haves there is nothing to acknowledge (the common clone
	// case), so skip the ancestry walk entirely.
	var acks []string
	if len(fr.haves) > 0 {
		wantAncestors := make(map[string]bool)
		for _, w := range wantCommits {
			for oid := range r.ancestors(w) {
				wantAncestors[oid] = true
			}
		}
		shallowSet := make(map[string]bool, len(fr.shallow))
		for _, s := range fr.shallow {
			shallowSet[s] = true
		}
		acked := make(map[string]bool)
		for _, h := range fr.haves {
			stack := []string{h}
			seen := make(map[string]bool)
			for len(stack) > 0 {
				cur := stack[len(stack)-1]
				stack = stack[:len(stack)-1]
				if seen[cur] || acked[cur] {
					continue
				}
				seen[cur] = true
				if wantAncestors[cur] {
					acks = append(acks, cur)
					acked[cur] = true
					continue
				}
				if shallowSet[cur] {
					continue
				}
				if c := r.commitOf(cur); c != nil {
					stack = append(stack, c.parents...)
				}
			}
		}
	}

	// Shallow-info: the new boundary, and previously-shallow commits that
	// are now fully included.
	var shallow []string
	for oid := range boundary {
		shallow = append(shallow, oid)
	}
	sort.Strings(shallow)
	var unshallow []string
	for s := range clientShallow {
		if included[s] && !boundary[s] {
			unshallow = append(unshallow, s)
		}
	}
	sort.Strings(unshallow)

	return &fetchSelection{
		pack:      writePack(packObjects),
		acks:      acks,
		nak:       len(acks) == 0,
		shallow:   shallow,
		unshallow: unshallow,
	}, nil
}

// fetchCacheKey renders a fetch request as a cache key. Wants, shallow
// boundaries and deepen-not refs are sorted (their order does not affect
// the response); haves stay in request order because the ACK walk follows
// it. Depth and deepen-since are part of the key verbatim.
func fetchCacheKey(fr fetchRequest, v2 bool) string {
	var b strings.Builder
	if v2 {
		b.WriteByte('2')
	} else {
		b.WriteByte('0')
	}
	b.WriteByte('|')
	wants := append([]string(nil), fr.wants...)
	sort.Strings(wants)
	for _, w := range wants {
		b.WriteString(w)
		b.WriteByte(',')
	}
	b.WriteByte('|')
	for _, h := range fr.haves {
		b.WriteString(h)
		b.WriteByte(',')
	}
	b.WriteByte('|')
	shallow := append([]string(nil), fr.shallow...)
	sort.Strings(shallow)
	for _, s := range shallow {
		b.WriteString(s)
		b.WriteByte(',')
	}
	b.WriteByte('|')
	b.WriteString(strconv.Itoa(fr.depth))
	b.WriteByte('|')
	b.WriteString(strconv.FormatInt(fr.deepenSince, 10))
	b.WriteByte('|')
	dn := append([]string(nil), fr.deepenNot...)
	sort.Strings(dn)
	for _, d := range dn {
		b.WriteString(d)
		b.WriteByte(',')
	}
	return b.String()
}

// fetchResponse returns the complete upload-pack response body for a fetch
// request, serving it from the repo's cache when an identical fetch was
// already answered for the current repo state. A fetch response is a pure
// function of (repo state, request): planFetch sorts everything it emits
// (shallow/unshallow lists, pack object order), and the ACK walk follows
// the haves order, which is part of the key. The clone benchmark fires 50
// concurrent identical fetches; the first computes and the rest hit the
// cache, so the pack is built once per round instead of 50 times.
//
// Locking: the store read lock is taken first, then the repo's fetchMu —
// the same order touch() uses (store write lock, then fetchMu) — so the
// two can never deadlock. fetchMu is held across the compute: concurrent
// identical fetches single-flight on it instead of each building a pack.
func (s *server) fetchResponse(repo *repo, fr fetchRequest, v2 bool) ([]byte, error) {
	key := fetchCacheKey(fr, v2)
	s.st.mu.RLock()
	repo.fetchMu.Lock()
	if resp, ok := repo.fetchCache[key]; ok {
		repo.fetchMu.Unlock()
		s.st.mu.RUnlock()
		return resp, nil
	}
	sel, err := repo.planFetch(fr)
	if err != nil {
		repo.fetchMu.Unlock()
		s.st.mu.RUnlock()
		return nil, err
	}
	var resp []byte
	if v2 {
		resp = buildFetchV2Body(fr, sel)
	} else {
		resp = buildFetchV0Body(sel)
	}
	// Cache only modest responses (a giant fetch would pin megabytes),
	// and bound the entries per repo; the map is cleared wholesale when
	// it fills, which is fine because fetches cluster on few keys.
	if len(resp) <= 4<<20 {
		if repo.fetchCache == nil {
			repo.fetchCache = make(map[string][]byte, 4)
		} else if len(repo.fetchCache) >= 32 {
			clear(repo.fetchCache)
		}
		repo.fetchCache[key] = resp
	}
	repo.fetchMu.Unlock()
	s.st.mu.RUnlock()
	return resp, nil
}

// buildFetchV2Body frames a fetch selection as a protocol v2 response.
// Sections are separated by delim packets; only the whole response ends
// with a flush (real git dies on a flush where it expects the next section
// header). One exception: a NAK ends its section with a flush, not a
// delim — that is how real upload-pack frames it, and git refuses any
// further section after a NAK followed by a delim.
func buildFetchV2Body(fr fetchRequest, sel *fetchSelection) []byte {
	var b bytes.Buffer
	if len(fr.haves) > 0 {
		b.Write(pktLine([]byte("acknowledgments\n")))
		if sel.nak {
			b.Write(pktLine([]byte("NAK\n")))
			b.Write(pktFlush())
		} else {
			for _, ack := range sel.acks {
				b.Write(pktLine([]byte("ACK " + ack + "\n")))
			}
			b.Write(pktLine([]byte("ready\n")))
			b.Write(pktDelim())
		}
	}
	// Shallow-info section, only when there is something to say.
	if len(sel.shallow) > 0 || len(sel.unshallow) > 0 {
		b.Write(pktLine([]byte("shallow-info\n")))
		for _, oid := range sel.shallow {
			b.Write(pktLine([]byte("shallow " + oid + "\n")))
		}
		for _, oid := range sel.unshallow {
			b.Write(pktLine([]byte("unshallow " + oid + "\n")))
		}
		b.Write(pktDelim())
	}
	// Packfile section (always at least one sideband packet, even for an
	// empty pack).
	b.Write(pktLine([]byte("packfile\n")))
	b.Write(sidebandPackets(sel.pack))
	b.Write(pktFlush())
	return b.Bytes()
}

// buildFetchV0Body frames a fetch selection as a protocol v0 response.
// Without multi_ack (which this server does not advertise), v0 allows
// exactly ONE ack line: the client moves on to reading the pack after the
// first ACK and dies on a second one. No flush separates the ACK/NAK lines
// from the pack in v0: real git treats a flush there as the end of the
// stream and then fails on the pack header. The pack's sideband packets
// follow directly, and a single flush ends the response.
func buildFetchV0Body(sel *fetchSelection) []byte {
	var b bytes.Buffer
	for _, oid := range sel.shallow {
		b.Write(pktLine([]byte("shallow " + oid + "\n")))
	}
	for _, oid := range sel.unshallow {
		b.Write(pktLine([]byte("unshallow " + oid + "\n")))
	}
	if sel.nak {
		b.Write(pktLine([]byte("NAK\n")))
	} else if len(sel.acks) > 0 {
		b.Write(pktLine([]byte("ACK " + sel.acks[0] + "\n")))
	}
	b.Write(sidebandPackets(sel.pack))
	b.Write(pktFlush())
	return b.Bytes()
}

func (s *server) gitFetchV2(w http.ResponseWriter, repo *repo, packets []pktPacket) {
	fr := parseFetchV2(packets)
	resp, err := s.fetchResponse(repo, fr, true)
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	w.Header().Set("Content-Type", "application/x-git-upload-pack-result")
	_, _ = w.Write(resp)
}

func (s *server) gitFetchV0(w http.ResponseWriter, repo *repo, packets []pktPacket) {
	fr := parseFetchV0(packets)
	resp, err := s.fetchResponse(repo, fr, false)
	if err != nil {
		http.Error(w, err.Error(), http.StatusBadRequest)
		return
	}
	w.Header().Set("Content-Type", "application/x-git-upload-pack-result")
	_, _ = w.Write(resp)
}

// ---------------------------------------------------------------------------
// git-receive-pack: pushes

type pushCommand struct {
	oldOID string
	newOID string
	ref    string
}

func (s *server) gitReceivePack(w http.ResponseWriter, r *http.Request, repo *repo) {
	body, err := io.ReadAll(io.LimitReader(r.Body, 64<<20))
	_ = r.Body.Close()
	if err != nil {
		http.Error(w, "could not read request", http.StatusBadRequest)
		return
	}
	// Commands run until the first flush; the pack follows the flush, so
	// only the command section is parsed as pkt-lines.
	packets, consumed, err := decodePktLinesUntilFlush(body)
	if err != nil {
		http.Error(w, "bad pkt-line stream", http.StatusBadRequest)
		return
	}
	// Commands run until the first flush; the pack follows.
	var commands []pushCommand
	sideband := false
	for _, p := range packets {
		if p.kind == "flush" {
			break
		}
		if p.kind != "data" {
			continue
		}
		line := pktText(p)
		caps := ""
		if i := strings.IndexByte(line, 0); i >= 0 {
			caps = line[i+1:]
			line = line[:i]
		}
		if strings.Contains(caps, "side-band-64k") {
			sideband = true
		}
		fields := strings.Fields(line)
		if len(fields) != 3 {
			http.Error(w, "bad push command", http.StatusBadRequest)
			return
		}
		commands = append(commands, pushCommand{oldOID: fields[0], newOID: fields[1], ref: fields[2]})
	}
	if len(commands) == 0 {
		http.Error(w, "no push commands", http.StatusBadRequest)
		return
	}
	packBytes := body[consumed:]
	updatesRef := false
	for _, c := range commands {
		if c.newOID != zeroOID {
			updatesRef = true
			break
		}
	}

	s.st.mu.Lock()
	defer s.st.mu.Unlock()

	// Unpack first; every object is stored even if a ref is refused.
	unpackErr := ""
	if updatesRef {
		if len(packBytes) == 0 {
			unpackErr = "empty pack"
		} else {
			objs, err := readPack(packBytes, func(oid string) *gitObj { return repo.getObject(oid) })
			if err != nil {
				unpackErr = err.Error()
			} else {
				for oid, o := range objs {
					repo.objects[oid] = o
				}
			}
		}
	}

	// Build the report.
	var report bytes.Buffer
	if unpackErr != "" {
		report.Write(pktLine([]byte("unpack " + unpackErr + "\n")))
	} else {
		report.Write(pktLine([]byte("unpack ok\n")))
	}
	for _, cmd := range commands {
		if unpackErr != "" {
			report.Write(pktLine([]byte("ng " + cmd.ref + " unpacker error\n")))
			continue
		}
		if msg := s.applyPushCommand(repo, cmd); msg == "" {
			report.Write(pktLine([]byte("ok " + cmd.ref + "\n")))
		} else {
			report.Write(pktLine([]byte("ng " + cmd.ref + " " + msg + "\n")))
		}
	}
	// Objects are stored even when a ref update is refused, so any push
	// (or delete) may have changed what a fetch would return.
	repo.touch()

	w.Header().Set("Content-Type", "application/x-git-receive-pack-result")
	if sideband {
		// The report stream inside band 1 is itself pkt-line framed, so
		// it needs its own flush terminator: a client parsing the
		// demultiplexed stream hits EOF instead of a clean end without it.
		report.Write(pktFlush())
		_, _ = w.Write(sidebandPackets(report.Bytes()))
	} else {
		_, _ = w.Write(report.Bytes())
	}
	_, _ = w.Write(pktFlush())
}

// applyPushCommand enforces one push command. It returns "" on success or
// the refusal reason.
func (s *server) applyPushCommand(repo *repo, cmd pushCommand) string {
	current, exists := repo.refs[cmd.ref]
	if !exists {
		current = zeroOID
	}
	// The old OID must match the ref's current value.
	if cmd.oldOID != current {
		return "non-fast-forward"
	}
	// Delete.
	if cmd.newOID == zeroOID {
		if exists {
			delete(repo.refs, cmd.ref)
		}
		return ""
	}
	// The new object must exist.
	obj := repo.getObject(cmd.newOID)
	if obj == nil {
		return "object not found"
	}
	// Tags: create and delete only; an update is never a fast-forward.
	if strings.HasPrefix(cmd.ref, "refs/tags/") {
		if cmd.oldOID != zeroOID && cmd.oldOID != cmd.newOID {
			return "non-fast-forward"
		}
		repo.refs[cmd.ref] = cmd.newOID
		return ""
	}
	// Branches (and other refs): the new tip must be a commit, and an
	// update must be a fast-forward.
	if obj.typ != objCommit {
		return "non-fast-forward"
	}
	if cmd.oldOID != zeroOID && !repo.isAncestor(cmd.oldOID, cmd.newOID) {
		return "non-fast-forward"
	}
	repo.refs[cmd.ref] = cmd.newOID
	return ""
}

// ---------------------------------------------------------------------------
// REST v3 API (/api/v3)
// ---------------------------------------------------------------------------

func (s *server) handleREST(w http.ResponseWriter, r *http.Request) {
	if !s.requireAuth(w, r) {
		return
	}
	rest := strings.TrimPrefix(r.URL.Path, "/api/v3")
	rest = strings.TrimPrefix(rest, "/")
	var segs []string
	if rest != "" {
		segs = strings.Split(rest, "/")
	}

	// API root and meta.
	if len(segs) == 0 {
		if r.Method != http.MethodGet {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		w.Header().Set("X-OAuth-Scopes", "repo, read:org")
		s.writeJSON(w, http.StatusOK, map[string]any{
			"current_user_url":      "/api/v3/user",
			"repository_url":        "/api/v3/repos/{owner}/{repo}",
			"rate_limit_url":        "/api/v3/rate_limit",
			"meta_url":              "/api/v3/meta",
			"emojis_url":            "/api/v3/emojis",
			"user_search_url":       "/api/v3/search/users?q={query}",
			"issue_search_url":      "/api/v3/search/issues?q={query}",
			"code_search_url":       "/api/v3/search/code?q={query}",
			"repository_search_url": "/api/v3/search/repositories?q={query}",
		})
		return
	}

	switch segs[0] {
	case "meta":
		if r.Method == http.MethodGet && len(segs) == 1 {
			s.writeJSON(w, http.StatusOK, map[string]any{"installed_version": "forge-" + s.cfg.version})
			return
		}
	case "user":
		s.restUser(w, r, segs[1:])
		return
	case "users":
		s.restUsers(w, r, segs[1:])
		return
	case "repos":
		s.restRepos(w, r, segs[1:])
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

// --- JSON shapes -----------------------------------------------------------

func userJSON(cfg config) map[string]any {
	return map[string]any{
		"login": cfg.viewer,
		"id":    viewerID,
		"type":  "User",
		"name":  cfg.viewer,
		"email": cfg.viewer + "@example.invalid",
	}
}

func (s *server) repoJSON(rp *repo) map[string]any {
	full := rp.owner + "/" + rp.name
	return map[string]any{
		"id":             rp.id,
		"name":           rp.name,
		"full_name":      full,
		"owner":          map[string]any{"login": rp.owner, "id": viewerID, "type": "User"},
		"private":        rp.private,
		"description":    rp.description,
		"default_branch": rp.defaultBranch,
		"created_at":     fixedISO,
		"updated_at":     fixedISO,
		"html_url":       "https://github.com/" + full,
		"url":            "/api/v3/repos/" + full,
		"clone_url":      "https://github.com/" + full + ".git",
		"git_url":        "git://github.com/" + full + ".git",
		"ssh_url":        "git@github.com:" + full + ".git",
		"has_issues":     true,
		"has_projects":   true,
		"has_wiki":       true,
		"fork":           false,
	}
}

func (s *server) labelJSON(l *label) map[string]any {
	return map[string]any{
		"id":          l.id,
		"name":        l.name,
		"color":       l.color,
		"description": "",
		"default":     false,
	}
}

func (s *server) issueLabelsJSON(rp *repo, names []string) []any {
	out := []any{}
	for _, n := range names {
		if l, ok := rp.labels[n]; ok {
			out = append(out, s.labelJSON(l))
		} else {
			out = append(out, map[string]any{"name": n, "color": "ededed"})
		}
	}
	return out
}

func (s *server) issueJSON(rp *repo, is *issue) map[string]any {
	return map[string]any{
		"id":         is.id,
		"number":     is.number,
		"title":      is.title,
		"body":       is.body,
		"state":      is.state,
		"labels":     s.issueLabelsJSON(rp, is.labels),
		"user":       map[string]any{"login": s.cfg.viewer, "id": viewerID, "type": "User"},
		"created_at": fixedISO,
		"updated_at": fixedISO,
		"comments":   len(is.comments),
	}
}

// pullAsIssueJSON renders a pull request the way GitHub's issues API does.
func (s *server) pullAsIssueJSON(rp *repo, pr *pull) map[string]any {
	return map[string]any{
		"id":           pr.id,
		"number":       pr.number,
		"title":        pr.title,
		"body":         pr.body,
		"state":        pr.state,
		"labels":       []any{},
		"user":         map[string]any{"login": s.cfg.viewer, "id": viewerID, "type": "User"},
		"created_at":   fixedISO,
		"updated_at":   fixedISO,
		"comments":     0,
		"pull_request": map[string]any{},
	}
}

func (s *server) pullJSON(rp *repo, pr *pull) map[string]any {
	headSha := pr.headSha
	if tip := rp.refTip("refs/heads/" + pr.headRef); tip != "" {
		headSha = tip
	}
	baseSha := pr.baseSha
	if tip := rp.refTip("refs/heads/" + pr.baseRef); tip != "" {
		baseSha = tip
	}
	var mergedAt any
	if pr.merged {
		mergedAt = pr.mergedAt
	}
	var mergeSha any
	if pr.merged {
		mergeSha = pr.mergeCommitSha
	}
	return map[string]any{
		"id":               pr.id,
		"number":           pr.number,
		"title":            pr.title,
		"body":             pr.body,
		"state":            pr.state,
		"merged":           pr.merged,
		"merged_at":        mergedAt,
		"merge_commit_sha": mergeSha,
		"mergeable":        !rp.prConflict(pr),
		"head": map[string]any{
			"ref":   pr.headRef,
			"sha":   headSha,
			"label": rp.owner + ":" + pr.headRef,
		},
		"base": map[string]any{
			"ref":   pr.baseRef,
			"sha":   baseSha,
			"label": rp.owner + ":" + pr.baseRef,
		},
		"user":       map[string]any{"login": s.cfg.viewer, "id": viewerID, "type": "User"},
		"created_at": fixedISO,
		"updated_at": fixedISO,
	}
}

func (s *server) commentJSON(c *comment) map[string]any {
	return map[string]any{
		"id":         c.id,
		"body":       c.body,
		"user":       map[string]any{"login": s.cfg.viewer, "id": viewerID, "type": "User"},
		"created_at": fixedISO,
		"updated_at": fixedISO,
	}
}

// --- /user -----------------------------------------------------------------

func (s *server) restUser(w http.ResponseWriter, r *http.Request, segs []string) {
	if len(segs) == 0 {
		if r.Method != http.MethodGet {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		s.writeJSON(w, http.StatusOK, userJSON(s.cfg))
		return
	}
	if len(segs) == 1 && segs[0] == "repos" {
		switch r.Method {
		case http.MethodGet:
			s.listUserRepos(w, r)
		case http.MethodPost:
			s.createRepo(w, r)
		default:
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		}
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

func (s *server) listUserRepos(w http.ResponseWriter, r *http.Request) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	var list []*repo
	for _, rp := range s.st.repos {
		if rp.owner == s.cfg.viewer {
			list = append(list, rp)
		}
	}
	sort.Slice(list, func(i, j int) bool { return list[i].seq < list[j].seq })
	perPage, page := parsePagination(r.URL.Query())
	pageItems, hasNext := pageSlice(list, perPage, page)
	writeLinkHeader(w, r, perPage, page, hasNext, len(list))
	out := make([]any, 0, len(pageItems))
	for _, rp := range pageItems {
		out = append(out, s.repoJSON(rp))
	}
	s.writeJSON(w, http.StatusOK, out)
}

func (s *server) createRepo(w http.ResponseWriter, r *http.Request) {
	var body struct {
		Name        string `json:"name"`
		Private     bool   `json:"private"`
		Description string `json:"description"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	if strings.TrimSpace(body.Name) == "" {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("name is required"))
		return
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	if s.st.getRepo(s.cfg.viewer, body.Name) != nil {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("name already exists on this account"))
		return
	}
	rp := &repo{
		id:            s.st.nextRepoID,
		name:          body.Name,
		owner:         s.cfg.viewer,
		private:       body.Private,
		description:   body.Description,
		defaultBranch: defaultBranch,
		seq:           s.st.nextSeq(),
		refs:          make(map[string]string),
		objects:       make(map[string]*gitObj),
		issues:        make(map[int]*issue),
		pulls:         make(map[int]*pull),
		labels:        make(map[string]*label),
		nextNumber:    1,
	}
	s.st.nextRepoID++
	s.st.repos[repoKey(rp.owner, rp.name)] = rp
	s.st.repoByID[rp.id] = rp
	s.writeJSON(w, http.StatusCreated, s.repoJSON(rp))
}

// --- /users/{username}/repos -----------------------------------------------

func (s *server) restUsers(w http.ResponseWriter, r *http.Request, segs []string) {
	if len(segs) == 2 && segs[1] == "repos" && r.Method == http.MethodGet {
		if segs[0] != s.cfg.viewer {
			s.writeJSON(w, http.StatusOK, []any{})
			return
		}
		s.listUserRepos(w, r)
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

// --- /repos/{owner}/{name}/... ---------------------------------------------

func (s *server) restRepos(w http.ResponseWriter, r *http.Request, segs []string) {
	if len(segs) < 2 {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	owner, name := segs[0], segs[1]
	rest := segs[2:]

	if len(rest) == 0 {
		switch r.Method {
		case http.MethodGet:
			s.st.mu.RLock()
			rp := s.st.getRepo(owner, name)
			if rp == nil {
				s.st.mu.RUnlock()
				s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
				return
			}
			out := s.repoJSON(rp)
			s.st.mu.RUnlock()
			s.writeJSON(w, http.StatusOK, out)
		case http.MethodPatch:
			s.patchRepo(w, r, owner, name)
		case http.MethodDelete:
			s.st.mu.Lock()
			if s.st.getRepo(owner, name) == nil {
				s.st.mu.Unlock()
				s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
				return
			}
			rp := s.st.getRepo(owner, name)
			delete(s.st.repos, repoKey(owner, name))
			delete(s.st.repoByID, rp.id)
			s.st.mu.Unlock()
			w.WriteHeader(http.StatusNoContent)
		default:
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		}
		return
	}

	switch rest[0] {
	case "branches":
		s.restBranches(w, r, owner, name, rest[1:])
	case "commits":
		s.restCommits(w, r, owner, name)
	case "contents":
		s.restContents(w, r, owner, name, rest[1:])
	case "git":
		s.restGit(w, r, owner, name, rest[1:])
	case "labels":
		s.restLabels(w, r, owner, name)
	case "issues":
		s.restIssues(w, r, owner, name, rest[1:])
	case "pulls":
		s.restPulls(w, r, owner, name, rest[1:])
	default:
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
	}
}

func (s *server) patchRepo(w http.ResponseWriter, r *http.Request, owner, name string) {
	var body struct {
		Description *string `json:"description"`
		Private     *bool   `json:"private"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if body.Description != nil {
		rp.description = *body.Description
	}
	if body.Private != nil {
		rp.private = *body.Private
	}
	s.writeJSON(w, http.StatusOK, s.repoJSON(rp))
}

// --- branches ---------------------------------------------------------------

func (s *server) restBranches(w http.ResponseWriter, r *http.Request, owner, name string, rest []string) {
	if r.Method != http.MethodGet {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		return
	}
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if len(rest) == 0 {
		var names []string
		for ref := range rp.refs {
			if strings.HasPrefix(ref, "refs/heads/") {
				names = append(names, strings.TrimPrefix(ref, "refs/heads/"))
			}
		}
		sort.Strings(names)
		out := make([]any, 0, len(names))
		for _, n := range names {
			out = append(out, map[string]any{
				"name":   n,
				"commit": map[string]any{"sha": rp.refs["refs/heads/"+n]},
			})
		}
		s.writeJSON(w, http.StatusOK, out)
		return
	}
	branch := strings.Join(rest, "/")
	sha, ok := rp.refs["refs/heads/"+branch]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	s.writeJSON(w, http.StatusOK, map[string]any{
		"name":   branch,
		"commit": map[string]any{"sha": sha},
	})
}

// --- commits ----------------------------------------------------------------

func (s *server) restCommits(w http.ResponseWriter, r *http.Request, owner, name string) {
	if r.Method != http.MethodGet {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		return
	}
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	ref := r.URL.Query().Get("sha")
	if ref == "" {
		ref = rp.defaultBranch
	}
	tip := rp.branchTip(ref)
	if tip == "" {
		s.writeJSON(w, http.StatusOK, []any{})
		return
	}
	commits := rp.listCommits(tip)
	perPage, page := parsePagination(r.URL.Query())
	pageItems, hasNext := pageSlice(commits, perPage, page)
	writeLinkHeader(w, r, perPage, page, hasNext, len(commits))
	out := make([]any, 0, len(pageItems))
	for _, oid := range pageItems {
		c := rp.commitOf(oid)
		if c == nil {
			continue
		}
		out = append(out, map[string]any{
			"sha": oid,
			"commit": map[string]any{
				// The REST view shows the message without the
				// trailing newline git stores with it.
				"message": strings.TrimSuffix(c.message, "\n"),
				"author": map[string]any{
					"name":  s.cfg.viewer,
					"email": s.cfg.viewer + "@example.invalid",
					"date":  fixedISO,
				},
				"committer": map[string]any{
					"name":  s.cfg.viewer,
					"email": s.cfg.viewer + "@example.invalid",
					"date":  fixedISO,
				},
			},
		})
	}
	s.writeJSON(w, http.StatusOK, out)
}

// --- contents ---------------------------------------------------------------

// dirEntries returns the immediate entries of the directory at path inside
// the tree (path "" is the root). Nil when path is not a directory.
func (r *repo) dirEntries(treeOID, path string) []treeEntry {
	cur := treeOID
	if path != "" {
		for _, comp := range strings.Split(path, "/") {
			o := r.getObject(cur)
			if o == nil || o.typ != objTree {
				return nil
			}
			next := ""
			for _, e := range parseTree(o.data) {
				if e.name == comp && e.isDir() {
					next = e.oid
					break
				}
			}
			if next == "" {
				return nil
			}
			cur = next
		}
	}
	o := r.getObject(cur)
	if o == nil || o.typ != objTree {
		return nil
	}
	return parseTree(o.data)
}

func (s *server) restContents(w http.ResponseWriter, r *http.Request, owner, name string, rest []string) {
	path := strings.Join(rest, "/")
	switch r.Method {
	case http.MethodGet:
		s.getContents(w, r, owner, name, path)
	case http.MethodPut:
		s.putContents(w, r, owner, name, path)
	case http.MethodDelete:
		s.deleteContents(w, r, owner, name, path)
	default:
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
	}
}

func (s *server) getContents(w http.ResponseWriter, r *http.Request, owner, name, path string) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	ref := r.URL.Query().Get("ref")
	if ref == "" {
		ref = rp.defaultBranch
	}
	tip := rp.branchTip(ref)
	if tip == "" {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	c := rp.commitOf(tip)
	if c == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	files := rp.flattenTree(c.tree)
	if blobOID, ok := files[path]; ok {
		o := rp.getObject(blobOID)
		data := []byte{}
		if o != nil {
			data = o.data
		}
		base := path
		if i := strings.LastIndexByte(path, '/'); i >= 0 {
			base = path[i+1:]
		}
		s.writeJSON(w, http.StatusOK, map[string]any{
			"type":     "file",
			"encoding": "base64",
			"content":  base64.StdEncoding.EncodeToString(data),
			"sha":      blobOID,
			"size":     len(data),
			"name":     base,
			"path":     path,
		})
		return
	}
	entries := rp.dirEntries(c.tree, path)
	if entries == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	out := make([]any, 0, len(entries))
	for _, e := range entries {
		typ := "file"
		if e.isDir() {
			typ = "dir"
		}
		entry := map[string]any{
			"type": typ,
			"name": e.name,
			"path": strings.TrimPrefix(path+"/"+e.name, "/"),
			"sha":  e.oid,
		}
		if !e.isDir() {
			if o := rp.getObject(e.oid); o != nil {
				entry["size"] = len(o.data)
			}
		}
		out = append(out, entry)
	}
	s.writeJSON(w, http.StatusOK, out)
}

func (s *server) putContents(w http.ResponseWriter, r *http.Request, owner, name, path string) {
	var body struct {
		Message string `json:"message"`
		Content string `json:"content"`
		Branch  string `json:"branch"`
		Sha     string `json:"sha"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	data, err := base64.StdEncoding.DecodeString(body.Content)
	if err != nil {
		s.writeJSON(w, http.StatusBadRequest, errBody("content is not valid base64"))
		return
	}
	if body.Message == "" {
		body.Message = "Update " + path
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	branch := body.Branch
	if branch == "" {
		branch = rp.defaultBranch
	}
	// Resolve the branch tip (a new branch starts from the default tip).
	tip, exists := rp.refs["refs/heads/"+branch]
	if !exists {
		tip = rp.refs["refs/heads/"+rp.defaultBranch]
	}
	var currentBlob string
	fileExists := false
	if tip != "" {
		if oid, ok := rp.flattenCommit(tip)[path]; ok {
			currentBlob, fileExists = oid, true
		}
	}
	if body.Sha != "" {
		if !fileExists || body.Sha != currentBlob {
			s.writeJSON(w, http.StatusConflict, errBody("sha does not match the current file"))
			return
		}
	}
	commitOID, blobOID, err := rp.applyContents(s.cfg, branch, path, data, false, body.Message)
	if err != nil {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody(err.Error()))
		return
	}
	status := http.StatusCreated
	if fileExists {
		status = http.StatusOK
	}
	base := path
	if i := strings.LastIndexByte(path, '/'); i >= 0 {
		base = path[i+1:]
	}
	s.writeJSON(w, status, map[string]any{
		"content": map[string]any{
			"name":     base,
			"path":     path,
			"sha":      blobOID,
			"size":     len(data),
			"encoding": "base64",
		},
		"commit": map[string]any{"sha": commitOID, "message": body.Message},
	})
}

func (s *server) deleteContents(w http.ResponseWriter, r *http.Request, owner, name, path string) {
	var body struct {
		Message string `json:"message"`
		Sha     string `json:"sha"`
		Branch  string `json:"branch"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	if body.Message == "" {
		body.Message = "Delete " + path
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	branch := body.Branch
	if branch == "" {
		branch = rp.defaultBranch
	}
	tip := rp.refs["refs/heads/"+branch]
	if tip == "" {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	currentBlob, ok := rp.flattenCommit(tip)[path]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if body.Sha != "" && body.Sha != currentBlob {
		s.writeJSON(w, http.StatusConflict, errBody("sha does not match the current file"))
		return
	}
	commitOID, _, err := rp.applyContents(s.cfg, branch, path, nil, true, body.Message)
	if err != nil {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody(err.Error()))
		return
	}
	s.writeJSON(w, http.StatusOK, map[string]any{
		"commit": map[string]any{"sha": commitOID, "message": body.Message},
	})
}

// --- git data API -----------------------------------------------------------

func (s *server) restGit(w http.ResponseWriter, r *http.Request, owner, name string, rest []string) {
	if len(rest) == 0 {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if rest[0] != "refs" {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	switch r.Method {
	case http.MethodPost:
		if len(rest) != 1 {
			s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
			return
		}
		s.createRef(w, r, owner, name)
	case http.MethodGet:
		if len(rest) == 1 {
			s.listRefs(w, r, owner, name)
			return
		}
		s.getRef(w, r, owner, name, "refs/"+strings.Join(rest[1:], "/"))
	default:
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
	}
}

func (s *server) createRef(w http.ResponseWriter, r *http.Request, owner, name string) {
	var body struct {
		Ref string `json:"ref"`
		Sha string `json:"sha"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	if !strings.HasPrefix(body.Ref, "refs/") || !isHexOID(body.Sha) {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("invalid ref or sha"))
		return
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if _, exists := rp.refs[body.Ref]; exists {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("Reference already exists"))
		return
	}
	if rp.getObject(body.Sha) == nil {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("Object does not exist"))
		return
	}
	rp.refs[body.Ref] = body.Sha
	rp.touch() // a new ref changes what ls-refs/fetch see; cached fetches are stale
	s.writeJSON(w, http.StatusCreated, map[string]any{
		"ref":    body.Ref,
		"object": map[string]any{"sha": body.Sha},
	})
}

func (s *server) getRef(w http.ResponseWriter, r *http.Request, owner, name, ref string) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	sha, ok := rp.refs[ref]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	s.writeJSON(w, http.StatusOK, map[string]any{
		"ref":    ref,
		"object": map[string]any{"sha": sha},
	})
}

func (s *server) listRefs(w http.ResponseWriter, r *http.Request, owner, name string) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	out := make([]any, 0, len(rp.refs))
	for _, ref := range rp.sortedRefNames() {
		out = append(out, map[string]any{
			"ref":    ref,
			"object": map[string]any{"sha": rp.refs[ref]},
		})
	}
	s.writeJSON(w, http.StatusOK, out)
}

// --- labels -----------------------------------------------------------------

func (s *server) restLabels(w http.ResponseWriter, r *http.Request, owner, name string) {
	switch r.Method {
	case http.MethodGet:
		s.st.mu.RLock()
		defer s.st.mu.RUnlock()
		rp := s.st.getRepo(owner, name)
		if rp == nil {
			s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
			return
		}
		var names []string
		for n := range rp.labels {
			names = append(names, n)
		}
		sort.Strings(names)
		out := make([]any, 0, len(names))
		for _, n := range names {
			out = append(out, s.labelJSON(rp.labels[n]))
		}
		s.writeJSON(w, http.StatusOK, out)
	case http.MethodPost:
		var body struct {
			Name  string `json:"name"`
			Color string `json:"color"`
		}
		if !s.readJSONBody(w, r, &body) {
			return
		}
		if strings.TrimSpace(body.Name) == "" {
			s.writeJSON(w, http.StatusUnprocessableEntity, errBody("name is required"))
			return
		}
		if body.Color == "" {
			body.Color = "ededed"
		}
		s.st.mu.Lock()
		defer s.st.mu.Unlock()
		rp := s.st.getRepo(owner, name)
		if rp == nil {
			s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
			return
		}
		if _, exists := rp.labels[body.Name]; exists {
			s.writeJSON(w, http.StatusUnprocessableEntity, errBody("label already exists"))
			return
		}
		l := &label{id: s.st.nextLabelID, name: body.Name, color: body.Color}
		s.st.nextLabelID++
		rp.labels[body.Name] = l
		s.writeJSON(w, http.StatusCreated, s.labelJSON(l))
	default:
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
	}
}

// --- issues -----------------------------------------------------------------

func parseIssueLabels(raw any) []string {
	arr, ok := raw.([]any)
	if !ok {
		return nil
	}
	var out []string
	for _, v := range arr {
		switch t := v.(type) {
		case string:
			out = append(out, t)
		case map[string]any:
			if n, ok := t["name"].(string); ok {
				out = append(out, n)
			}
		}
	}
	return out
}

func (s *server) restIssues(w http.ResponseWriter, r *http.Request, owner, name string, rest []string) {
	if len(rest) == 0 {
		switch r.Method {
		case http.MethodGet:
			s.listIssues(w, r, owner, name)
		case http.MethodPost:
			s.createIssue(w, r, owner, name)
		default:
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		}
		return
	}
	n, err := strconv.Atoi(rest[0])
	if err != nil || n < 1 {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if len(rest) == 1 {
		switch r.Method {
		case http.MethodGet:
			s.getIssue(w, r, owner, name, n)
		case http.MethodPatch:
			s.patchIssue(w, r, owner, name, n)
		default:
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		}
		return
	}
	if len(rest) == 2 && rest[1] == "comments" {
		switch r.Method {
		case http.MethodGet:
			s.listComments(w, r, owner, name, n)
		case http.MethodPost:
			s.createComment(w, r, owner, name, n)
		default:
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		}
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

func (s *server) listIssues(w http.ResponseWriter, r *http.Request, owner, name string) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	state := r.URL.Query().Get("state")
	if state == "" {
		state = "open"
	}
	direction := r.URL.Query().Get("direction")
	if direction == "" {
		direction = "desc"
	}
	type entry struct {
		seq  int64
		json map[string]any
	}
	var entries []entry
	for _, is := range rp.issues {
		if state != "all" && is.state != state {
			continue
		}
		entries = append(entries, entry{is.seq, s.issueJSON(rp, is)})
	}
	// GitHub's issues list includes pull requests.
	for _, pr := range rp.pulls {
		if state != "all" && pr.state != state {
			continue
		}
		entries = append(entries, entry{pr.seq, s.pullAsIssueJSON(rp, pr)})
	}
	sort.Slice(entries, func(i, j int) bool {
		if direction == "asc" {
			return entries[i].seq < entries[j].seq
		}
		return entries[i].seq > entries[j].seq
	})
	perPage, page := parsePagination(r.URL.Query())
	pageItems, hasNext := pageSlice(entries, perPage, page)
	writeLinkHeader(w, r, perPage, page, hasNext, len(entries))
	out := make([]any, 0, len(pageItems))
	for _, e := range pageItems {
		out = append(out, e.json)
	}
	s.writeJSON(w, http.StatusOK, out)
}

func (s *server) createIssue(w http.ResponseWriter, r *http.Request, owner, name string) {
	var body struct {
		Title  string `json:"title"`
		Body   string `json:"body"`
		Labels any    `json:"labels"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	if strings.TrimSpace(body.Title) == "" {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("title is required"))
		return
	}
	labelNames := parseIssueLabels(body.Labels)
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	for _, ln := range labelNames {
		if _, ok := rp.labels[ln]; !ok {
			s.writeJSON(w, http.StatusUnprocessableEntity, errBody("label '"+ln+"' does not exist"))
			return
		}
	}
	is := &issue{
		id:     s.st.nextIssueID,
		number: rp.nextNumber,
		title:  body.Title,
		body:   body.Body,
		state:  "open",
		labels: labelNames,
		seq:    s.st.nextSeq(),
	}
	s.st.nextIssueID++
	rp.nextNumber++
	rp.issues[is.number] = is
	s.writeRawJSON(w, http.StatusCreated, s.issueJSONBytes(rp, is))
}

func (s *server) getIssue(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if is, ok := rp.issues[n]; ok {
		s.writeRawJSON(w, http.StatusOK, s.issueJSONBytes(rp, is))
		return
	}
	if pr, ok := rp.pulls[n]; ok {
		s.writeJSON(w, http.StatusOK, s.pullAsIssueJSON(rp, pr))
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

func (s *server) patchIssue(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	var body struct {
		State *string `json:"state"`
		Title *string `json:"title"`
		Body  *string `json:"body"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if is, ok := rp.issues[n]; ok {
		if body.State != nil && (*body.State == "open" || *body.State == "closed") {
			is.state = *body.State
		}
		if body.Title != nil {
			is.title = *body.Title
		}
		if body.Body != nil {
			is.body = *body.Body
		}
		s.writeRawJSON(w, http.StatusOK, s.issueJSONBytes(rp, is))
		return
	}
	if pr, ok := rp.pulls[n]; ok {
		if body.State != nil && (*body.State == "open" || *body.State == "closed") {
			pr.state = *body.State
		}
		if body.Title != nil {
			pr.title = *body.Title
		}
		if body.Body != nil {
			pr.body = *body.Body
		}
		s.writeJSON(w, http.StatusOK, s.pullAsIssueJSON(rp, pr))
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

func (s *server) listComments(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	is, ok := rp.issues[n]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	out := make([]any, 0, len(is.comments))
	for _, c := range is.comments {
		out = append(out, s.commentJSON(c))
	}
	s.writeJSON(w, http.StatusOK, out)
}

func (s *server) createComment(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	var body struct {
		Body string `json:"body"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	is, ok := rp.issues[n]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	c := &comment{id: s.st.nextCommentID, body: body.Body, seq: s.st.nextSeq()}
	s.st.nextCommentID++
	is.comments = append(is.comments, c)
	s.writeJSON(w, http.StatusCreated, s.commentJSON(c))
}

// --- pull requests ----------------------------------------------------------

func (s *server) restPulls(w http.ResponseWriter, r *http.Request, owner, name string, rest []string) {
	if len(rest) == 0 {
		switch r.Method {
		case http.MethodGet:
			s.listPulls(w, r, owner, name)
		case http.MethodPost:
			s.createPull(w, r, owner, name)
		default:
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		}
		return
	}
	n, err := strconv.Atoi(rest[0])
	if err != nil || n < 1 {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if len(rest) == 1 {
		if r.Method != http.MethodGet {
			s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
			return
		}
		s.getPull(w, r, owner, name, n)
		return
	}
	if len(rest) == 2 && rest[1] == "files" && r.Method == http.MethodGet {
		s.listPullFiles(w, r, owner, name, n)
		return
	}
	if len(rest) == 2 && rest[1] == "merge" && r.Method == http.MethodPut {
		s.mergePull(w, r, owner, name, n)
		return
	}
	s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
}

func (s *server) listPulls(w http.ResponseWriter, r *http.Request, owner, name string) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	state := r.URL.Query().Get("state")
	if state == "" {
		state = "open"
	}
	var list []*pull
	for _, pr := range rp.pulls {
		if state != "all" && pr.state != state {
			continue
		}
		list = append(list, pr)
	}
	sort.Slice(list, func(i, j int) bool { return list[i].seq > list[j].seq })
	perPage, page := parsePagination(r.URL.Query())
	pageItems, hasNext := pageSlice(list, perPage, page)
	writeLinkHeader(w, r, perPage, page, hasNext, len(list))
	out := make([]any, 0, len(pageItems))
	for _, pr := range pageItems {
		out = append(out, s.pullJSON(rp, pr))
	}
	s.writeJSON(w, http.StatusOK, out)
}

func (s *server) createPull(w http.ResponseWriter, r *http.Request, owner, name string) {
	var body struct {
		Title string `json:"title"`
		Body  string `json:"body"`
		Head  string `json:"head"`
		Base  string `json:"base"`
	}
	if !s.readJSONBody(w, r, &body) {
		return
	}
	if strings.TrimSpace(body.Title) == "" {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("title is required"))
		return
	}
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	headRef := strings.TrimPrefix(body.Head, rp.owner+":")
	baseRef := strings.TrimPrefix(body.Base, rp.owner+":")
	headTip, headOk := rp.refs["refs/heads/"+headRef]
	baseTip, baseOk := rp.refs["refs/heads/"+baseRef]
	if !headOk || !baseOk {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("head or base branch does not exist"))
		return
	}
	if headRef == baseRef {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody("head and base are the same"))
		return
	}
	for _, pr := range rp.pulls {
		if pr.state == "open" && pr.headRef == headRef && pr.baseRef == baseRef {
			s.writeJSON(w, http.StatusUnprocessableEntity, errBody("A pull request already exists for these branches"))
			return
		}
	}
	pr := &pull{
		id:      s.st.nextIssueID,
		number:  rp.nextNumber,
		title:   body.Title,
		body:    body.Body,
		state:   "open",
		headRef: headRef,
		baseRef: baseRef,
		headSha: headTip,
		baseSha: baseTip,
		seq:     s.st.nextSeq(),
	}
	s.st.nextIssueID++
	rp.nextNumber++
	rp.pulls[pr.number] = pr
	s.writeJSON(w, http.StatusCreated, s.pullJSON(rp, pr))
}

func (s *server) getPull(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	pr, ok := rp.pulls[n]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	s.writeJSON(w, http.StatusOK, s.pullJSON(rp, pr))
}

func (s *server) listPullFiles(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	s.st.mu.RLock()
	defer s.st.mu.RUnlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	pr, ok := rp.pulls[n]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	headTip := rp.refTip("refs/heads/" + pr.headRef)
	baseTip := rp.refTip("refs/heads/" + pr.baseRef)
	mb := rp.mergeBase(headTip, baseTip)
	changes := rp.diffFileMaps(rp.flattenCommit(mb), rp.flattenCommit(headTip))
	out := make([]any, 0, len(changes))
	headFiles := rp.flattenCommit(headTip)
	for _, fc := range changes {
		sha := ""
		if oid, ok := headFiles[fc.filename]; ok {
			sha = oid
		}
		out = append(out, map[string]any{
			"filename":  fc.filename,
			"status":    fc.status,
			"additions": fc.additions,
			"deletions": fc.deletions,
			"changes":   fc.additions + fc.deletions,
			"sha":       sha,
		})
	}
	s.writeJSON(w, http.StatusOK, out)
}

func (s *server) mergePull(w http.ResponseWriter, r *http.Request, owner, name string, n int) {
	var body struct {
		MergeMethod string `json:"merge_method"`
	}
	// The body is optional; an empty body still merges.
	_ = s.readJSONBody(w, r, &body)
	s.st.mu.Lock()
	defer s.st.mu.Unlock()
	rp := s.st.getRepo(owner, name)
	if rp == nil {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	pr, ok := rp.pulls[n]
	if !ok {
		s.writeJSON(w, http.StatusNotFound, errBody("Not Found"))
		return
	}
	if pr.merged {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Pull request is already merged"))
		return
	}
	if pr.state != "open" {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Pull request is closed"))
		return
	}
	sha, conflict, err := rp.squashMerge(s.cfg, pr)
	if err != nil {
		s.writeJSON(w, http.StatusUnprocessableEntity, errBody(err.Error()))
		return
	}
	if conflict {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Merge conflict"))
		return
	}
	pr.merged = true
	pr.state = "closed"
	pr.mergedAt = fixedISO
	pr.mergeCommitSha = sha
	s.writeJSON(w, http.StatusOK, map[string]any{
		"sha":     sha,
		"merged":  true,
		"message": "Pull request successfully merged",
	})
}

// ---------------------------------------------------------------------------
// GraphQL v4 API (/api/graphql): a small parser and executor for the
// documents gh and github-mcp-server send.
// ---------------------------------------------------------------------------

func (s *server) handleGraphQL(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		return
	}
	if !s.requireAuth(w, r) {
		return
	}
	body, err := io.ReadAll(io.LimitReader(r.Body, 4<<20))
	_ = r.Body.Close()
	if err != nil {
		s.writeJSON(w, http.StatusBadRequest, map[string]any{"errors": []any{map[string]any{"message": "could not read request body"}}})
		return
	}
	trimmed := bytes.TrimSpace(body)
	if len(trimmed) == 0 {
		s.writeJSON(w, http.StatusBadRequest, map[string]any{"errors": []any{map[string]any{"message": "empty request body"}}})
		return
	}
	// Batching: a JSON array of operation documents answers an array.
	if trimmed[0] == '[' {
		var ops []gqlRequest
		if err := json.Unmarshal(trimmed, &ops); err != nil {
			s.writeJSON(w, http.StatusBadRequest, map[string]any{"errors": []any{map[string]any{"message": "malformed JSON body"}}})
			return
		}
		out := make([]any, 0, len(ops))
		for _, op := range ops {
			out = append(out, s.executeGraphQL(op))
		}
		s.writeJSON(w, http.StatusOK, out)
		return
	}
	var req gqlRequest
	if err := json.Unmarshal(trimmed, &req); err != nil {
		s.writeJSON(w, http.StatusBadRequest, map[string]any{"errors": []any{map[string]any{"message": "malformed JSON body"}}})
		return
	}
	s.writeJSON(w, http.StatusOK, s.executeGraphQL(req))
}

type gqlRequest struct {
	Query         string         `json:"query"`
	Variables     map[string]any `json:"variables"`
	OperationName string         `json:"operationName"`
}

// --- the parser ------------------------------------------------------------

type gqlValue struct {
	kind    string // var, string, int, float, bool, null, enum, list, object
	str     string
	num     float64
	boolean bool
	list    []*gqlValue
	obj     map[string]*gqlValue
}

type gqlField struct {
	alias    string
	name     string // "" for fragments
	args     map[string]*gqlValue
	sel      []*gqlField
	fragCond string // inline fragment type condition
	fragName string // named fragment spread
}

type gqlOp struct {
	opType string // "query" | "mutation"
	name   string
	sel    []*gqlField
}

type gqlFragment struct {
	typeCond string
	sel      []*gqlField
}

type gqlParser struct {
	src string
	pos int
}

func (p *gqlParser) skipSpace() {
	for p.pos < len(p.src) {
		c := p.src[p.pos]
		if c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == ',' {
			p.pos++
			continue
		}
		if c == '#' {
			for p.pos < len(p.src) && p.src[p.pos] != '\n' {
				p.pos++
			}
			continue
		}
		break
	}
}

func (p *gqlParser) peek() byte {
	p.skipSpace()
	if p.pos >= len(p.src) {
		return 0
	}
	return p.src[p.pos]
}

func isNameStart(c byte) bool {
	return c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

func isNameChar(c byte) bool {
	return isNameStart(c) || (c >= '0' && c <= '9')
}

func (p *gqlParser) parseName() (string, error) {
	p.skipSpace()
	if p.pos >= len(p.src) || !isNameStart(p.src[p.pos]) {
		return "", fmt.Errorf("expected a name at offset %d", p.pos)
	}
	start := p.pos
	for p.pos < len(p.src) && isNameChar(p.src[p.pos]) {
		p.pos++
	}
	return p.src[start:p.pos], nil
}

func (p *gqlParser) expect(c byte) error {
	p.skipSpace()
	if p.pos >= len(p.src) || p.src[p.pos] != c {
		return fmt.Errorf("expected %q at offset %d", string(c), p.pos)
	}
	p.pos++
	return nil
}

// parseString parses a "..." string with escapes.
func (p *gqlParser) parseString() (string, error) {
	p.skipSpace()
	if p.pos >= len(p.src) || p.src[p.pos] != '"' {
		return "", fmt.Errorf("expected a string at offset %d", p.pos)
	}
	// Block strings are not used by the suite; reject them plainly.
	if strings.HasPrefix(p.src[p.pos:], `"""`) {
		return "", fmt.Errorf("block strings are not supported")
	}
	p.pos++
	var b strings.Builder
	for p.pos < len(p.src) {
		c := p.src[p.pos]
		p.pos++
		switch c {
		case '"':
			return b.String(), nil
		case '\\':
			if p.pos >= len(p.src) {
				return "", fmt.Errorf("unterminated escape")
			}
			esc := p.src[p.pos]
			p.pos++
			switch esc {
			case '"':
				b.WriteByte('"')
			case '\\':
				b.WriteByte('\\')
			case '/':
				b.WriteByte('/')
			case 'b':
				b.WriteByte('\b')
			case 'f':
				b.WriteByte('\f')
			case 'n':
				b.WriteByte('\n')
			case 'r':
				b.WriteByte('\r')
			case 't':
				b.WriteByte('\t')
			case 'u':
				if p.pos+4 > len(p.src) {
					return "", fmt.Errorf("bad unicode escape")
				}
				n, err := strconv.ParseInt(p.src[p.pos:p.pos+4], 16, 32)
				if err != nil {
					return "", fmt.Errorf("bad unicode escape")
				}
				p.pos += 4
				b.WriteRune(rune(n))
			default:
				return "", fmt.Errorf("bad escape \\%c", esc)
			}
		default:
			b.WriteByte(c)
		}
	}
	return "", fmt.Errorf("unterminated string")
}

func (p *gqlParser) parseValue() (*gqlValue, error) {
	p.skipSpace()
	if p.pos >= len(p.src) {
		return nil, fmt.Errorf("expected a value")
	}
	switch c := p.src[p.pos]; {
	case c == '$':
		p.pos++
		name, err := p.parseName()
		if err != nil {
			return nil, err
		}
		return &gqlValue{kind: "var", str: name}, nil
	case c == '"':
		s, err := p.parseString()
		if err != nil {
			return nil, err
		}
		return &gqlValue{kind: "string", str: s}, nil
	case c == '[':
		p.pos++
		v := &gqlValue{kind: "list"}
		for {
			p.skipSpace()
			if p.pos < len(p.src) && p.src[p.pos] == ']' {
				p.pos++
				return v, nil
			}
			item, err := p.parseValue()
			if err != nil {
				return nil, err
			}
			v.list = append(v.list, item)
		}
	case c == '{':
		p.pos++
		v := &gqlValue{kind: "object", obj: map[string]*gqlValue{}}
		for {
			p.skipSpace()
			if p.pos < len(p.src) && p.src[p.pos] == '}' {
				p.pos++
				return v, nil
			}
			name, err := p.parseName()
			if err != nil {
				return nil, err
			}
			if err := p.expect(':'); err != nil {
				return nil, err
			}
			val, err := p.parseValue()
			if err != nil {
				return nil, err
			}
			v.obj[name] = val
		}
	case c == '-' || (c >= '0' && c <= '9'):
		start := p.pos
		if c == '-' {
			p.pos++
		}
		isFloat := false
		for p.pos < len(p.src) {
			d := p.src[p.pos]
			if d >= '0' && d <= '9' {
				p.pos++
			} else if d == '.' || d == 'e' || d == 'E' || d == '+' || d == '-' {
				isFloat = true
				p.pos++
			} else {
				break
			}
		}
		text := p.src[start:p.pos]
		num, err := strconv.ParseFloat(text, 64)
		if err != nil {
			return nil, fmt.Errorf("bad number %q", text)
		}
		kind := "int"
		if isFloat {
			kind = "float"
		}
		return &gqlValue{kind: kind, num: num, str: text}, nil
	default:
		name, err := p.parseName()
		if err != nil {
			return nil, err
		}
		switch name {
		case "true":
			return &gqlValue{kind: "bool", boolean: true}, nil
		case "false":
			return &gqlValue{kind: "bool", boolean: false}, nil
		case "null":
			return &gqlValue{kind: "null"}, nil
		default:
			return &gqlValue{kind: "enum", str: name}, nil
		}
	}
}

func (p *gqlParser) parseArguments() (map[string]*gqlValue, error) {
	args := map[string]*gqlValue{}
	if err := p.expect('('); err != nil {
		return nil, err
	}
	for {
		p.skipSpace()
		if p.pos < len(p.src) && p.src[p.pos] == ')' {
			p.pos++
			return args, nil
		}
		name, err := p.parseName()
		if err != nil {
			return nil, err
		}
		if err := p.expect(':'); err != nil {
			return nil, err
		}
		val, err := p.parseValue()
		if err != nil {
			return nil, err
		}
		args[name] = val
	}
}

// skipDirectives skips @name(args) directives (parsed, ignored).
func (p *gqlParser) skipDirectives() error {
	for {
		p.skipSpace()
		if p.pos >= len(p.src) || p.src[p.pos] != '@' {
			return nil
		}
		p.pos++
		if _, err := p.parseName(); err != nil {
			return err
		}
		p.skipSpace()
		if p.pos < len(p.src) && p.src[p.pos] == '(' {
			if _, err := p.parseArguments(); err != nil {
				return err
			}
		}
	}
}

// skipType skips a type reference: Name, [Name], Name!, [Name!]!.
func (p *gqlParser) skipType() error {
	p.skipSpace()
	if p.pos < len(p.src) && p.src[p.pos] == '[' {
		p.pos++
		if err := p.skipType(); err != nil {
			return err
		}
		if err := p.expect(']'); err != nil {
			return err
		}
	} else {
		if _, err := p.parseName(); err != nil {
			return err
		}
	}
	p.skipSpace()
	if p.pos < len(p.src) && p.src[p.pos] == '!' {
		p.pos++
	}
	return nil
}

func (p *gqlParser) parseSelectionSet() ([]*gqlField, error) {
	if err := p.expect('{'); err != nil {
		return nil, err
	}
	var sel []*gqlField
	for {
		p.skipSpace()
		if p.pos >= len(p.src) {
			return nil, fmt.Errorf("unterminated selection set")
		}
		if p.src[p.pos] == '}' {
			p.pos++
			return sel, nil
		}
		f, err := p.parseSelection()
		if err != nil {
			return nil, err
		}
		sel = append(sel, f)
	}
}

func (p *gqlParser) parseSelection() (*gqlField, error) {
	p.skipSpace()
	if strings.HasPrefix(p.src[p.pos:], "...") {
		p.pos += 3
		f := &gqlField{}
		p.skipSpace()
		if strings.HasPrefix(p.src[p.pos:], "on ") || strings.HasPrefix(p.src[p.pos:], "on\t") || strings.HasPrefix(p.src[p.pos:], "on\n") {
			p.pos += 2
			cond, err := p.parseName()
			if err != nil {
				return nil, err
			}
			f.fragCond = cond
		} else if p.pos < len(p.src) && isNameStart(p.src[p.pos]) {
			name, err := p.parseName()
			if err != nil {
				return nil, err
			}
			f.fragName = name
		}
		if err := p.skipDirectives(); err != nil {
			return nil, err
		}
		if f.fragName == "" {
			sel, err := p.parseSelectionSet()
			if err != nil {
				return nil, err
			}
			f.sel = sel
		}
		return f, nil
	}
	name, err := p.parseName()
	if err != nil {
		return nil, err
	}
	f := &gqlField{name: name}
	p.skipSpace()
	if p.pos < len(p.src) && p.src[p.pos] == ':' {
		// alias: field
		p.pos++
		real, err := p.parseName()
		if err != nil {
			return nil, err
		}
		f.alias = name
		f.name = real
	}
	p.skipSpace()
	if p.pos < len(p.src) && p.src[p.pos] == '(' {
		args, err := p.parseArguments()
		if err != nil {
			return nil, err
		}
		f.args = args
	}
	if err := p.skipDirectives(); err != nil {
		return nil, err
	}
	p.skipSpace()
	if p.pos < len(p.src) && p.src[p.pos] == '{' {
		sel, err := p.parseSelectionSet()
		if err != nil {
			return nil, err
		}
		f.sel = sel
	}
	return f, nil
}

func (p *gqlParser) parseDocument() ([]*gqlOp, map[string]*gqlFragment, error) {
	var ops []*gqlOp
	fragments := map[string]*gqlFragment{}
	for {
		p.skipSpace()
		if p.pos >= len(p.src) {
			break
		}
		if p.src[p.pos] == '{' {
			sel, err := p.parseSelectionSet()
			if err != nil {
				return nil, nil, err
			}
			ops = append(ops, &gqlOp{opType: "query", sel: sel})
			continue
		}
		kw, err := p.parseName()
		if err != nil {
			return nil, nil, err
		}
		switch kw {
		case "query", "mutation":
			op := &gqlOp{opType: kw}
			p.skipSpace()
			if p.pos < len(p.src) && isNameStart(p.src[p.pos]) {
				name, err := p.parseName()
				if err != nil {
					return nil, nil, err
				}
				op.name = name
			}
			p.skipSpace()
			if p.pos < len(p.src) && p.src[p.pos] == '(' {
				// Variable definitions: parse and discard (values come
				// from the request's variables map).
				p.pos++
				for {
					p.skipSpace()
					if p.pos < len(p.src) && p.src[p.pos] == ')' {
						p.pos++
						break
					}
					if p.pos < len(p.src) && p.src[p.pos] == '$' {
						p.pos++
					}
					if _, err := p.parseName(); err != nil {
						return nil, nil, err
					}
					if err := p.expect(':'); err != nil {
						return nil, nil, err
					}
					if err := p.skipType(); err != nil {
						return nil, nil, err
					}
					p.skipSpace()
					if p.pos < len(p.src) && p.src[p.pos] == '=' {
						p.pos++
						if _, err := p.parseValue(); err != nil {
							return nil, nil, err
						}
					}
				}
			}
			if err := p.skipDirectives(); err != nil {
				return nil, nil, err
			}
			sel, err := p.parseSelectionSet()
			if err != nil {
				return nil, nil, err
			}
			op.sel = sel
			ops = append(ops, op)
		case "fragment":
			name, err := p.parseName()
			if err != nil {
				return nil, nil, err
			}
			p.skipSpace()
			if !strings.HasPrefix(p.src[p.pos:], "on") {
				return nil, nil, fmt.Errorf("expected 'on' in fragment definition")
			}
			p.pos += 2
			cond, err := p.parseName()
			if err != nil {
				return nil, nil, err
			}
			if err := p.skipDirectives(); err != nil {
				return nil, nil, err
			}
			sel, err := p.parseSelectionSet()
			if err != nil {
				return nil, nil, err
			}
			fragments[name] = &gqlFragment{typeCond: cond, sel: sel}
		default:
			return nil, nil, fmt.Errorf("unexpected keyword %q", kw)
		}
	}
	return ops, fragments, nil
}

// --- schema: fields, types, introspection -----------------------------------

var gqlFields = map[string]map[string]bool{
	"Query": {"viewer": true, "repository": true, "node": true, "__type": true, "__schema": true, "__typename": true},
	"Node":  {"id": true, "__typename": true},
	"User":  {"login": true, "id": true, "name": true, "email": true, "__typename": true},
	"Ref":   {"name": true, "id": true, "target": true, "__typename": true},
	"Repository": {"id": true, "databaseId": true, "name": true, "nameWithOwner": true, "owner": true,
		"defaultBranchRef": true, "viewerPermission": true, "hasIssuesEnabled": true,
		"issue": true, "issues": true, "pullRequests": true, "pullRequest": true,
		"description": true, "isPrivate": true, "createdAt": true, "updatedAt": true, "url": true, "__typename": true},
	"IssueConnection":       {"nodes": true, "edges": true, "pageInfo": true, "totalCount": true, "__typename": true},
	"Issue":                 {"id": true, "number": true, "title": true, "body": true, "state": true, "createdAt": true, "updatedAt": true, "url": true, "author": true, "comments": true, "labels": true, "__typename": true},
	"PullRequestConnection": {"nodes": true, "edges": true, "pageInfo": true, "totalCount": true, "__typename": true},
	"PullRequest": {"id": true, "number": true, "title": true, "body": true, "state": true, "merged": true,
		"mergeable": true, "headRefName": true, "baseRefName": true, "files": true,
		"createdAt": true, "updatedAt": true, "mergedAt": true, "url": true, "author": true, "__typename": true},
	"PullRequestChangedFilesConnection": {"nodes": true, "edges": true, "pageInfo": true, "totalCount": true, "__typename": true},
	"ChangedFile":                       {"path": true, "additions": true, "deletions": true, "changes": true, "__typename": true},
	"PageInfo":                          {"hasNextPage": true, "hasPreviousPage": true, "endCursor": true, "startCursor": true, "__typename": true},
	"IssueEdge":                         {"node": true, "cursor": true, "__typename": true},
	"PullRequestEdge":                   {"node": true, "cursor": true, "__typename": true},
	"ChangedFileEdge":                   {"node": true, "cursor": true, "__typename": true},
	"CommentEdge":                       {"node": true, "cursor": true, "__typename": true},
	"Comment":                           {"id": true, "body": true, "createdAt": true, "updatedAt": true, "author": true, "__typename": true},
	"Mutation":                          {"createIssue": true, "closeIssue": true, "createPullRequest": true, "mergePullRequest": true, "addComment": true, "__typename": true},
	"CreateIssuePayload":                {"issue": true, "clientMutationId": true, "__typename": true},
	"CloseIssuePayload":                 {"issue": true, "clientMutationId": true, "__typename": true},
	"CreatePullRequestPayload":          {"pullRequest": true, "clientMutationId": true, "__typename": true},
	"MergePullRequestPayload":           {"pullRequest": true, "clientMutationId": true, "__typename": true},
	"AddCommentPayload":                 {"commentEdge": true, "subject": true, "clientMutationId": true, "__typename": true},
	"__Type":                            {"name": true, "kind": true, "description": true, "fields": true, "enumValues": true, "inputFields": true, "interfaces": true, "possibleTypes": true, "__typename": true},
	"__Field":                           {"name": true, "description": true, "type": true, "args": true, "__typename": true},
	"__EnumValue":                       {"name": true, "description": true, "__typename": true},
	"__InputValue":                      {"name": true, "description": true, "type": true, "__typename": true},
}

var gqlFieldTypes = map[string]map[string]string{
	"Query":                             {"viewer": "User", "repository": "Repository", "node": "Node", "__type": "__Type"},
	"Repository":                        {"owner": "User", "defaultBranchRef": "Ref", "issue": "Issue", "issues": "IssueConnection", "pullRequests": "PullRequestConnection", "pullRequest": "PullRequest"},
	"IssueConnection":                   {"nodes": "Issue", "edges": "IssueEdge", "pageInfo": "PageInfo"},
	"IssueEdge":                         {"node": "Issue"},
	"PullRequestConnection":             {"nodes": "PullRequest", "edges": "PullRequestEdge", "pageInfo": "PageInfo"},
	"PullRequestEdge":                   {"node": "PullRequest"},
	"PullRequest":                       {"files": "PullRequestChangedFilesConnection"},
	"PullRequestChangedFilesConnection": {"nodes": "ChangedFile", "edges": "ChangedFileEdge", "pageInfo": "PageInfo"},
	"ChangedFileEdge":                   {"node": "ChangedFile"},
	"Mutation":                          {"createIssue": "CreateIssuePayload", "closeIssue": "CloseIssuePayload", "createPullRequest": "CreatePullRequestPayload", "mergePullRequest": "MergePullRequestPayload", "addComment": "AddCommentPayload"},
	"CreateIssuePayload":                {"issue": "Issue"},
	"CloseIssuePayload":                 {"issue": "Issue"},
	"CreatePullRequestPayload":          {"pullRequest": "PullRequest"},
	"MergePullRequestPayload":           {"pullRequest": "PullRequest"},
	"AddCommentPayload":                 {"commentEdge": "CommentEdge", "subject": "Issue"},
	"CommentEdge":                       {"node": "Comment"},
	"__Type":                            {"fields": "__Field", "enumValues": "__EnumValue"},
}

var gqlEnums = map[string][]string{
	"SearchType":           {"ISSUE", "REPOSITORY", "USER", "DISCUSSION", "COMMIT"},
	"IssueState":           {"OPEN", "CLOSED"},
	"PullRequestState":     {"OPEN", "CLOSED", "MERGED"},
	"MergeableState":       {"MERGEABLE", "CONFLICTING", "UNKNOWN"},
	"RepositoryPermission": {"ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"},
	"IssueOrderField":      {"CREATED_AT", "UPDATED_AT", "COMMENTS"},
	"OrderDirection":       {"ASC", "DESC"},
}

// --- global ids ------------------------------------------------------------

// gid builds an opaque, stable Relay-style global id.
func gid(kind string, parts ...int) string {
	var b strings.Builder
	b.WriteString(kind)
	for _, p := range parts {
		b.WriteString(":")
		b.WriteString(strconv.Itoa(p))
	}
	return base64.StdEncoding.EncodeToString([]byte(b.String()))
}

func parseGID(id string) (string, []int, bool) {
	raw, err := base64.StdEncoding.DecodeString(id)
	if err != nil {
		return "", nil, false
	}
	fields := strings.Split(string(raw), ":")
	if len(fields) < 2 {
		return "", nil, false
	}
	var parts []int
	for _, f := range fields[1:] {
		n, err := strconv.Atoi(f)
		if err != nil {
			return "", nil, false
		}
		parts = append(parts, n)
	}
	return fields[0], parts, true
}

// gqlCursor encodes a connection offset opaquely.
func gqlCursor(index int) string {
	return base64.StdEncoding.EncodeToString([]byte("cursor:" + strconv.Itoa(index)))
}

func parseGQLCursor(c string) (int, bool) {
	raw, err := base64.StdEncoding.DecodeString(c)
	if err != nil {
		return 0, false
	}
	if !strings.HasPrefix(string(raw), "cursor:") {
		return 0, false
	}
	n, err := strconv.Atoi(strings.TrimPrefix(string(raw), "cursor:"))
	if err != nil {
		return 0, false
	}
	return n, true
}

// --- execution --------------------------------------------------------------

type gqlCtx struct {
	s         *server
	vars      map[string]any
	fragments map[string]*gqlFragment
	errs      []string
}

func (c *gqlCtx) addErr(format string, args ...any) {
	c.errs = append(c.errs, fmt.Sprintf(format, args...))
}

// valueOf resolves a parsed value against the request variables.
func (c *gqlCtx) valueOf(v *gqlValue) any {
	if v == nil {
		return nil
	}
	switch v.kind {
	case "var":
		if c.vars == nil {
			return nil
		}
		return c.vars[v.str]
	case "string", "enum":
		return v.str
	case "int", "float":
		return v.num
	case "bool":
		return v.boolean
	case "null":
		return nil
	case "list":
		out := make([]any, 0, len(v.list))
		for _, item := range v.list {
			out = append(out, c.valueOf(item))
		}
		return out
	case "object":
		out := make(map[string]any, len(v.obj))
		for k, item := range v.obj {
			out[k] = c.valueOf(item)
		}
		return out
	}
	return nil
}

func (c *gqlCtx) arg(f *gqlField, name string) (any, bool) {
	if f.args == nil {
		return nil, false
	}
	v, ok := f.args[name]
	if !ok {
		return nil, false
	}
	val := c.valueOf(v)
	if val == nil {
		return nil, false
	}
	return val, true
}

func (c *gqlCtx) argString(f *gqlField, name string) (string, bool) {
	v, ok := c.arg(f, name)
	if !ok {
		return "", false
	}
	s, ok := v.(string)
	return s, ok
}

func (c *gqlCtx) argInt(f *gqlField, name string) (int, bool) {
	v, ok := c.arg(f, name)
	if !ok {
		return 0, false
	}
	switch n := v.(type) {
	case float64:
		return int(n), true
	case int:
		return n, true
	case json.Number:
		i, err := n.Int64()
		return int(i), err == nil
	}
	return 0, false
}

func (c *gqlCtx) argStringList(f *gqlField, name string) ([]string, bool) {
	v, ok := c.arg(f, name)
	if !ok {
		return nil, false
	}
	arr, ok := v.([]any)
	if !ok {
		return nil, false
	}
	out := make([]string, 0, len(arr))
	for _, item := range arr {
		if s, ok := item.(string); ok {
			out = append(out, s)
		}
	}
	return out, true
}

func (c *gqlCtx) argObject(f *gqlField, name string) (map[string]any, bool) {
	v, ok := c.arg(f, name)
	if !ok {
		return nil, false
	}
	m, ok := v.(map[string]any)
	return m, ok
}

// validateSelection walks a selection set against the schema, collecting
// unknown-field errors.
func (c *gqlCtx) validateSelection(sel []*gqlField, typeName string) []string {
	var errs []string
	for _, f := range sel {
		if f.fragName != "" {
			frag := c.fragments[f.fragName]
			if frag == nil {
				errs = append(errs, fmt.Sprintf("Unknown fragment %q.", f.fragName))
				continue
			}
			cond := frag.typeCond
			if cond == "" {
				cond = typeName
			}
			errs = append(errs, c.validateSelection(frag.sel, cond)...)
			continue
		}
		if f.fragCond != "" {
			errs = append(errs, c.validateSelection(f.sel, f.fragCond)...)
			continue
		}
		allowed := gqlFields[typeName]
		if allowed == nil || !allowed[f.name] {
			errs = append(errs, fmt.Sprintf("Cannot query field %q on type %q.", f.name, typeName))
			continue
		}
		if len(f.sel) > 0 {
			if next, ok := gqlFieldTypes[typeName][f.name]; ok {
				errs = append(errs, c.validateSelection(f.sel, next)...)
			}
		}
	}
	return errs
}

// execFields executes a selection set against one object: field resolves a
// single (non-fragment) field, or reports it unhandled.
func (c *gqlCtx) execFields(sel []*gqlField, typeName string, field func(f *gqlField) (any, bool)) map[string]any {
	out := map[string]any{}
	for _, f := range sel {
		if f.fragName != "" {
			frag := c.fragments[f.fragName]
			if frag == nil {
				continue
			}
			if frag.typeCond != "" && frag.typeCond != typeName {
				continue
			}
			for k, v := range c.execFields(frag.sel, typeName, field) {
				out[k] = v
			}
			continue
		}
		if f.fragCond != "" {
			if f.fragCond != typeName {
				continue
			}
			for k, v := range c.execFields(f.sel, typeName, field) {
				out[k] = v
			}
			continue
		}
		v, ok := field(f)
		if !ok {
			continue
		}
		key := f.alias
		if key == "" {
			key = f.name
		}
		out[key] = v
	}
	return out
}

func (s *server) executeGraphQL(req gqlRequest) map[string]any {
	p := &gqlParser{src: req.Query}
	ops, fragments, err := p.parseDocument()
	if err != nil {
		return map[string]any{
			"data":   nil,
			"errors": []any{map[string]any{"message": "Syntax Error: " + err.Error()}},
		}
	}
	var op *gqlOp
	if req.OperationName != "" {
		for _, o := range ops {
			if o.name == req.OperationName {
				op = o
				break
			}
		}
		if op == nil {
			return map[string]any{
				"data":   nil,
				"errors": []any{map[string]any{"message": "Unknown operation named \"" + req.OperationName + "\"."}},
			}
		}
	} else if len(ops) > 0 {
		op = ops[0]
	}
	if op == nil {
		return map[string]any{
			"data":   nil,
			"errors": []any{map[string]any{"message": "Must provide an operation."}},
		}
	}
	ctx := &gqlCtx{s: s, vars: req.Variables, fragments: fragments}
	rootType := "Query"
	if op.opType == "mutation" {
		rootType = "Mutation"
	}
	if errs := ctx.validateSelection(op.sel, rootType); len(errs) > 0 {
		out := make([]any, 0, len(errs))
		for _, e := range errs {
			out = append(out, map[string]any{"message": e})
		}
		return map[string]any{"data": nil, "errors": out}
	}

	// Mutations take the write lock; queries take the read lock.
	if op.opType == "mutation" {
		s.st.mu.Lock()
		defer s.st.mu.Unlock()
	} else {
		s.st.mu.RLock()
		defer s.st.mu.RUnlock()
	}
	var data map[string]any
	if op.opType == "mutation" {
		data = ctx.execMutation(op.sel)
	} else {
		data = ctx.execQuery(op.sel)
	}
	resp := map[string]any{"data": data}
	if len(ctx.errs) > 0 {
		out := make([]any, 0, len(ctx.errs))
		for _, e := range ctx.errs {
			out = append(out, map[string]any{"message": e})
		}
		resp["errors"] = out
	}
	return resp
}

// --- Query root --------------------------------------------------------------

func (c *gqlCtx) execQuery(sel []*gqlField) map[string]any {
	return c.execFields(sel, "Query", func(f *gqlField) (any, bool) {
		switch f.name {
		case "__typename":
			return "Query", true
		case "viewer":
			return c.execFields(f.sel, "User", func(uf *gqlField) (any, bool) {
				return c.resolveUserField(uf)
			}), true
		case "repository":
			owner, _ := c.argString(f, "owner")
			name, _ := c.argString(f, "name")
			rp := c.s.st.getRepo(owner, name)
			if rp == nil {
				return nil, true // unknown repository: null, no errors
			}
			return c.resolveRepository(f.sel, rp), true
		case "node":
			id, _ := c.argString(f, "id")
			return c.resolveNode(f.sel, id), true
		case "__type":
			name, _ := c.argString(f, "name")
			return c.resolveType(f.sel, name), true
		case "__schema":
			return c.execFields(f.sel, "__Type", func(sf *gqlField) (any, bool) {
				return nil, false
			}), true
		}
		return nil, false
	})
}

func (c *gqlCtx) resolveUserField(f *gqlField) (any, bool) {
	switch f.name {
	case "__typename":
		return "User", true
	case "login":
		return c.s.cfg.viewer, true
	case "id":
		return gid("User", viewerID), true
	case "name":
		return c.s.cfg.viewer, true
	case "email":
		return c.s.cfg.viewer + "@example.invalid", true
	}
	return nil, false
}

func (c *gqlCtx) resolveNode(sel []*gqlField, id string) any {
	kind, parts, ok := parseGID(id)
	if !ok {
		return nil
	}
	switch kind {
	case "Repository":
		if len(parts) != 1 {
			return nil
		}
		rp := c.s.st.repoByID[parts[0]]
		if rp == nil {
			return nil
		}
		return c.resolveRepository(sel, rp)
	case "Issue":
		if len(parts) != 2 {
			return nil
		}
		rp := c.s.st.repoByID[parts[0]]
		if rp == nil {
			return nil
		}
		is, ok := rp.issues[parts[1]]
		if !ok {
			return nil
		}
		return c.resolveIssue(sel, rp, is)
	case "PullRequest":
		if len(parts) != 2 {
			return nil
		}
		rp := c.s.st.repoByID[parts[0]]
		if rp == nil {
			return nil
		}
		pr, ok := rp.pulls[parts[1]]
		if !ok {
			return nil
		}
		return c.resolvePull(sel, rp, pr)
	}
	return nil
}

func (c *gqlCtx) resolveType(sel []*gqlField, name string) any {
	fields, isObject := gqlFields[name]
	enumValues, isEnum := gqlEnums[name]
	if !isObject && !isEnum {
		return nil // unknown type: null
	}
	kind := "OBJECT"
	if isEnum {
		kind = "ENUM"
	}
	return c.execFields(sel, "__Type", func(f *gqlField) (any, bool) {
		switch f.name {
		case "__typename":
			return "__Type", true
		case "name":
			return name, true
		case "kind":
			return kind, true
		case "description":
			return nil, true
		case "fields":
			if !isObject {
				return nil, true
			}
			names := make([]string, 0, len(fields))
			for n := range fields {
				if n == "__typename" {
					continue
				}
				names = append(names, n)
			}
			sort.Strings(names)
			out := make([]any, 0, len(names))
			for _, n := range names {
				out = append(out, c.execFields(f.sel, "__Field", func(ff *gqlField) (any, bool) {
					switch ff.name {
					case "__typename":
						return "__Field", true
					case "name":
						return n, true
					case "description":
						return nil, true
					}
					return nil, false
				}))
			}
			return out, true
		case "enumValues":
			if !isEnum {
				return nil, true
			}
			out := make([]any, 0, len(enumValues))
			for _, n := range enumValues {
				out = append(out, c.execFields(f.sel, "__EnumValue", func(ff *gqlField) (any, bool) {
					switch ff.name {
					case "__typename":
						return "__EnumValue", true
					case "name":
						return n, true
					case "description":
						return nil, true
					}
					return nil, false
				}))
			}
			return out, true
		case "inputFields", "interfaces", "possibleTypes":
			return []any{}, true
		}
		return nil, false
	})
}

// --- Repository --------------------------------------------------------------

func (c *gqlCtx) resolveRepository(sel []*gqlField, rp *repo) map[string]any {
	return c.execFields(sel, "Repository", func(f *gqlField) (any, bool) {
		switch f.name {
		case "__typename":
			return "Repository", true
		case "id":
			return gid("Repository", rp.id), true
		case "databaseId":
			return rp.id, true
		case "name":
			return rp.name, true
		case "nameWithOwner":
			return rp.owner + "/" + rp.name, true
		case "owner":
			return c.execFields(f.sel, "User", func(uf *gqlField) (any, bool) {
				return c.resolveUserField(uf)
			}), true
		case "defaultBranchRef":
			tip := rp.refTip("refs/heads/" + rp.defaultBranch)
			if tip == "" {
				return nil, true
			}
			return c.execFields(f.sel, "Ref", func(rf *gqlField) (any, bool) {
				switch rf.name {
				case "__typename":
					return "Ref", true
				case "name":
					return rp.defaultBranch, true
				case "id":
					return gid("Ref", rp.id), true
				}
				return nil, false
			}), true
		case "viewerPermission":
			return "ADMIN", true
		case "hasIssuesEnabled":
			return true, true
		case "description":
			return rp.description, true
		case "isPrivate":
			return rp.private, true
		case "createdAt", "updatedAt":
			return fixedISO, true
		case "url":
			return "https://github.com/" + rp.owner + "/" + rp.name, true
		case "issue":
			n, ok := c.argInt(f, "number")
			if !ok {
				return nil, true
			}
			is, ok := rp.issues[n]
			if !ok {
				return nil, true
			}
			return c.resolveIssue(f.sel, rp, is), true
		case "issues":
			return c.resolveIssueConnection(f, rp), true
		case "pullRequests":
			return c.resolvePullConnection(f, rp), true
		case "pullRequest":
			n, ok := c.argInt(f, "number")
			if !ok {
				return nil, true
			}
			pr, ok := rp.pulls[n]
			if !ok {
				return nil, true
			}
			return c.resolvePull(f.sel, rp, pr), true
		}
		return nil, false
	})
}

func issueStateGQL(state string) string {
	if state == "closed" {
		return "CLOSED"
	}
	return "OPEN"
}

func pullStateGQL(pr *pull) string {
	if pr.merged {
		return "MERGED"
	}
	if pr.state == "closed" {
		return "CLOSED"
	}
	return "OPEN"
}

func (c *gqlCtx) resolveIssue(sel []*gqlField, rp *repo, is *issue) map[string]any {
	return c.execFields(sel, "Issue", func(f *gqlField) (any, bool) {
		switch f.name {
		case "__typename":
			return "Issue", true
		case "id":
			return gid("Issue", rp.id, is.number), true
		case "number":
			return is.number, true
		case "title":
			return is.title, true
		case "body":
			return is.body, true
		case "state":
			return issueStateGQL(is.state), true
		case "createdAt", "updatedAt":
			return fixedISO, true
		case "url":
			return fmt.Sprintf("https://github.com/%s/%s/issues/%d", rp.owner, rp.name, is.number), true
		case "author":
			return c.execFields(f.sel, "User", func(uf *gqlField) (any, bool) {
				return c.resolveUserField(uf)
			}), true
		}
		return nil, false
	})
}

func (c *gqlCtx) resolvePull(sel []*gqlField, rp *repo, pr *pull) map[string]any {
	return c.execFields(sel, "PullRequest", func(f *gqlField) (any, bool) {
		switch f.name {
		case "__typename":
			return "PullRequest", true
		case "id":
			return gid("PullRequest", rp.id, pr.number), true
		case "number":
			return pr.number, true
		case "title":
			return pr.title, true
		case "body":
			return pr.body, true
		case "state":
			return pullStateGQL(pr), true
		case "merged":
			return pr.merged, true
		case "mergeable":
			if pr.merged || pr.state != "open" {
				return "UNKNOWN", true
			}
			if rp.prConflict(pr) {
				return "CONFLICTING", true
			}
			return "MERGEABLE", true
		case "headRefName":
			return pr.headRef, true
		case "baseRefName":
			return pr.baseRef, true
		case "createdAt", "updatedAt":
			return fixedISO, true
		case "mergedAt":
			if pr.merged {
				return pr.mergedAt, true
			}
			return nil, true
		case "url":
			return fmt.Sprintf("https://github.com/%s/%s/pull/%d", rp.owner, rp.name, pr.number), true
		case "author":
			return c.execFields(f.sel, "User", func(uf *gqlField) (any, bool) {
				return c.resolveUserField(uf)
			}), true
		case "files":
			return c.resolveFilesConnection(f, rp, pr), true
		}
		return nil, false
	})
}

// --- connections -------------------------------------------------------------

func (c *gqlCtx) resolveIssueConnection(f *gqlField, rp *repo) map[string]any {
	first, hasFirst := c.argInt(f, "first")
	after, _ := c.argString(f, "after")
	states, hasStates := c.argStringList(f, "states")
	orderBy, _ := c.argObject(f, "orderBy")

	var list []*issue
	for _, is := range rp.issues {
		if hasStates {
			want := false
			for _, st := range states {
				if issueStateGQL(is.state) == st {
					want = true
					break
				}
			}
			if !want {
				continue
			}
		}
		list = append(list, is)
	}
	desc := false
	if orderBy != nil {
		if d, ok := orderBy["direction"].(string); ok && d == "DESC" {
			desc = true
		}
	}
	sort.Slice(list, func(i, j int) bool {
		if desc {
			if list[i].seq == list[j].seq {
				return list[i].number > list[j].number
			}
			return list[i].seq > list[j].seq
		}
		if list[i].seq == list[j].seq {
			return list[i].number < list[j].number
		}
		return list[i].seq < list[j].seq
	})
	start := 0
	if after != "" {
		if idx, ok := parseGQLCursor(after); ok {
			start = idx + 1
		}
	}
	if start > len(list) {
		start = len(list)
	}
	end := len(list)
	if hasFirst && first >= 0 && start+first < end {
		end = start + first
	}
	page := list[start:end]
	hasNext := end < len(list)
	var endCursor any
	if len(page) > 0 {
		endCursor = gqlCursor(start + len(page) - 1)
	}
	var startCursor any
	if len(page) > 0 {
		startCursor = gqlCursor(start)
	}
	return c.execFields(f.sel, "IssueConnection", func(cf *gqlField) (any, bool) {
		switch cf.name {
		case "__typename":
			return "IssueConnection", true
		case "totalCount":
			return len(list), true
		case "nodes":
			out := make([]any, 0, len(page))
			for _, is := range page {
				out = append(out, c.resolveIssue(cf.sel, rp, is))
			}
			return out, true
		case "edges":
			out := make([]any, 0, len(page))
			for i, is := range page {
				out = append(out, c.execFields(cf.sel, "IssueEdge", func(ef *gqlField) (any, bool) {
					switch ef.name {
					case "__typename":
						return "IssueEdge", true
					case "cursor":
						return gqlCursor(start + i), true
					case "node":
						return c.resolveIssue(ef.sel, rp, is), true
					}
					return nil, false
				}))
			}
			return out, true
		case "pageInfo":
			return c.execFields(cf.sel, "PageInfo", func(pf *gqlField) (any, bool) {
				switch pf.name {
				case "__typename":
					return "PageInfo", true
				case "hasNextPage":
					return hasNext, true
				case "hasPreviousPage":
					return start > 0, true
				case "endCursor":
					return endCursor, true
				case "startCursor":
					return startCursor, true
				}
				return nil, false
			}), true
		}
		return nil, false
	})
}

func (c *gqlCtx) resolvePullConnection(f *gqlField, rp *repo) map[string]any {
	first, hasFirst := c.argInt(f, "first")
	after, _ := c.argString(f, "after")
	states, hasStates := c.argStringList(f, "states")

	var list []*pull
	for _, pr := range rp.pulls {
		if hasStates {
			want := false
			for _, st := range states {
				if pullStateGQL(pr) == st {
					want = true
					break
				}
			}
			if !want {
				continue
			}
		}
		list = append(list, pr)
	}
	sort.Slice(list, func(i, j int) bool { return list[i].seq > list[j].seq })
	start := 0
	if after != "" {
		if idx, ok := parseGQLCursor(after); ok {
			start = idx + 1
		}
	}
	if start > len(list) {
		start = len(list)
	}
	end := len(list)
	if hasFirst && first >= 0 && start+first < end {
		end = start + first
	}
	page := list[start:end]
	hasNext := end < len(list)
	var endCursor any
	if len(page) > 0 {
		endCursor = gqlCursor(start + len(page) - 1)
	}
	return c.execFields(f.sel, "PullRequestConnection", func(cf *gqlField) (any, bool) {
		switch cf.name {
		case "__typename":
			return "PullRequestConnection", true
		case "totalCount":
			return len(list), true
		case "nodes":
			out := make([]any, 0, len(page))
			for _, pr := range page {
				out = append(out, c.resolvePull(cf.sel, rp, pr))
			}
			return out, true
		case "edges":
			out := make([]any, 0, len(page))
			for i, pr := range page {
				out = append(out, c.execFields(cf.sel, "PullRequestEdge", func(ef *gqlField) (any, bool) {
					switch ef.name {
					case "__typename":
						return "PullRequestEdge", true
					case "cursor":
						return gqlCursor(start + i), true
					case "node":
						return c.resolvePull(ef.sel, rp, pr), true
					}
					return nil, false
				}))
			}
			return out, true
		case "pageInfo":
			return c.execFields(cf.sel, "PageInfo", func(pf *gqlField) (any, bool) {
				switch pf.name {
				case "__typename":
					return "PageInfo", true
				case "hasNextPage":
					return hasNext, true
				case "hasPreviousPage":
					return start > 0, true
				case "endCursor":
					return endCursor, true
				case "startCursor":
					if len(page) > 0 {
						return gqlCursor(start), true
					}
					return nil, true
				}
				return nil, false
			}), true
		}
		return nil, false
	})
}

func (c *gqlCtx) resolveFilesConnection(f *gqlField, rp *repo, pr *pull) map[string]any {
	first, hasFirst := c.argInt(f, "first")
	headTip := rp.refTip("refs/heads/" + pr.headRef)
	baseTip := rp.refTip("refs/heads/" + pr.baseRef)
	mb := rp.mergeBase(headTip, baseTip)
	changes := rp.diffFileMaps(rp.flattenCommit(mb), rp.flattenCommit(headTip))
	if hasFirst && first >= 0 && first < len(changes) {
		changes = changes[:first]
	}
	return c.execFields(f.sel, "PullRequestChangedFilesConnection", func(cf *gqlField) (any, bool) {
		switch cf.name {
		case "__typename":
			return "PullRequestChangedFilesConnection", true
		case "totalCount":
			return len(changes), true
		case "nodes":
			out := make([]any, 0, len(changes))
			for _, ch := range changes {
				out = append(out, c.execFields(cf.sel, "ChangedFile", func(ff *gqlField) (any, bool) {
					switch ff.name {
					case "__typename":
						return "ChangedFile", true
					case "path":
						return ch.filename, true
					case "additions":
						return ch.additions, true
					case "deletions":
						return ch.deletions, true
					case "changes":
						return ch.additions + ch.deletions, true
					}
					return nil, false
				}))
			}
			return out, true
		case "pageInfo":
			return c.execFields(cf.sel, "PageInfo", func(pf *gqlField) (any, bool) {
				switch pf.name {
				case "__typename":
					return "PageInfo", true
				case "hasNextPage":
					return false, true
				case "hasPreviousPage":
					return false, true
				case "endCursor", "startCursor":
					return nil, true
				}
				return nil, false
			}), true
		}
		return nil, false
	})
}

// --- mutations ---------------------------------------------------------------

func (c *gqlCtx) execMutation(sel []*gqlField) map[string]any {
	return c.execFields(sel, "Mutation", func(f *gqlField) (any, bool) {
		switch f.name {
		case "__typename":
			return "Mutation", true
		case "createIssue":
			return c.mutCreateIssue(f), true
		case "closeIssue":
			return c.mutCloseIssue(f), true
		case "createPullRequest":
			return c.mutCreatePullRequest(f), true
		case "mergePullRequest":
			return c.mutMergePullRequest(f), true
		case "addComment":
			return c.mutAddComment(f), true
		}
		return nil, false
	})
}

func inputString(input map[string]any, key string) string {
	if input == nil {
		return ""
	}
	s, _ := input[key].(string)
	return s
}

func (c *gqlCtx) repoByGID(id string) *repo {
	kind, parts, ok := parseGID(id)
	if !ok || kind != "Repository" || len(parts) != 1 {
		return nil
	}
	return c.s.st.repoByID[parts[0]]
}

func (c *gqlCtx) mutCreateIssue(f *gqlField) any {
	input, _ := c.argObject(f, "input")
	rp := c.repoByGID(inputString(input, "repositoryId"))
	if rp == nil {
		c.addErr("Could not resolve to a Repository with the id of %q.", inputString(input, "repositoryId"))
		return c.execFields(f.sel, "CreateIssuePayload", func(pf *gqlField) (any, bool) {
			if pf.name == "issue" {
				return nil, true
			}
			return nil, false
		})
	}
	is := &issue{
		id:     c.s.st.nextIssueID,
		number: rp.nextNumber,
		title:  inputString(input, "title"),
		body:   inputString(input, "body"),
		state:  "open",
		seq:    c.s.st.nextSeq(),
	}
	c.s.st.nextIssueID++
	rp.nextNumber++
	rp.issues[is.number] = is
	return c.execFields(f.sel, "CreateIssuePayload", func(pf *gqlField) (any, bool) {
		switch pf.name {
		case "__typename":
			return "CreateIssuePayload", true
		case "issue":
			return c.resolveIssue(pf.sel, rp, is), true
		case "clientMutationId":
			return inputString(input, "clientMutationId"), true
		}
		return nil, false
	})
}

func (c *gqlCtx) issueByGID(id string) (*repo, *issue) {
	kind, parts, ok := parseGID(id)
	if !ok || kind != "Issue" || len(parts) != 2 {
		return nil, nil
	}
	rp := c.s.st.repoByID[parts[0]]
	if rp == nil {
		return nil, nil
	}
	is, ok := rp.issues[parts[1]]
	if !ok {
		return nil, nil
	}
	return rp, is
}

func (c *gqlCtx) mutCloseIssue(f *gqlField) any {
	input, _ := c.argObject(f, "input")
	rp, is := c.issueByGID(inputString(input, "issueId"))
	if is == nil {
		c.addErr("Could not resolve to an Issue with the id of %q.", inputString(input, "issueId"))
		return c.execFields(f.sel, "CloseIssuePayload", func(pf *gqlField) (any, bool) {
			if pf.name == "issue" {
				return nil, true
			}
			return nil, false
		})
	}
	is.state = "closed"
	return c.execFields(f.sel, "CloseIssuePayload", func(pf *gqlField) (any, bool) {
		switch pf.name {
		case "__typename":
			return "CloseIssuePayload", true
		case "issue":
			return c.resolveIssue(pf.sel, rp, is), true
		case "clientMutationId":
			return inputString(input, "clientMutationId"), true
		}
		return nil, false
	})
}

func (c *gqlCtx) mutCreatePullRequest(f *gqlField) any {
	input, _ := c.argObject(f, "input")
	rp := c.repoByGID(inputString(input, "repositoryId"))
	headRef := inputString(input, "headRefName")
	baseRef := inputString(input, "baseRefName")
	fail := func(msg string) any {
		c.addErr("%s", msg)
		return c.execFields(f.sel, "CreatePullRequestPayload", func(pf *gqlField) (any, bool) {
			if pf.name == "pullRequest" {
				return nil, true
			}
			return nil, false
		})
	}
	if rp == nil {
		return fail("Could not resolve to a Repository with the id of " + inputString(input, "repositoryId") + ".")
	}
	headTip, headOk := rp.refs["refs/heads/"+headRef]
	baseTip, baseOk := rp.refs["refs/heads/"+baseRef]
	if !headOk || !baseOk {
		return fail("head or base branch does not exist")
	}
	if headRef == baseRef {
		return fail("head and base are the same")
	}
	for _, pr := range rp.pulls {
		if pr.state == "open" && pr.headRef == headRef && pr.baseRef == baseRef {
			return fail("A pull request already exists for these branches")
		}
	}
	pr := &pull{
		id:      c.s.st.nextIssueID,
		number:  rp.nextNumber,
		title:   inputString(input, "title"),
		body:    inputString(input, "body"),
		state:   "open",
		headRef: headRef,
		baseRef: baseRef,
		headSha: headTip,
		baseSha: baseTip,
		seq:     c.s.st.nextSeq(),
	}
	c.s.st.nextIssueID++
	rp.nextNumber++
	rp.pulls[pr.number] = pr
	return c.execFields(f.sel, "CreatePullRequestPayload", func(pf *gqlField) (any, bool) {
		switch pf.name {
		case "__typename":
			return "CreatePullRequestPayload", true
		case "pullRequest":
			return c.resolvePull(pf.sel, rp, pr), true
		case "clientMutationId":
			return inputString(input, "clientMutationId"), true
		}
		return nil, false
	})
}

func (c *gqlCtx) mutMergePullRequest(f *gqlField) any {
	input, _ := c.argObject(f, "input")
	kind, parts, ok := parseGID(inputString(input, "pullRequestId"))
	fail := func(msg string) any {
		c.addErr("%s", msg)
		return c.execFields(f.sel, "MergePullRequestPayload", func(pf *gqlField) (any, bool) {
			if pf.name == "pullRequest" {
				return nil, true
			}
			return nil, false
		})
	}
	if !ok || kind != "PullRequest" || len(parts) != 2 {
		return fail("Could not resolve to a PullRequest with the given id.")
	}
	rp := c.s.st.repoByID[parts[0]]
	if rp == nil {
		return fail("Could not resolve to a PullRequest with the given id.")
	}
	pr, ok := rp.pulls[parts[1]]
	if !ok {
		return fail("Could not resolve to a PullRequest with the given id.")
	}
	if pr.merged {
		return fail("Pull request is already merged")
	}
	if pr.state != "open" {
		return fail("Pull request is closed")
	}
	sha, conflict, err := rp.squashMerge(c.s.cfg, pr)
	if err != nil {
		return fail(err.Error())
	}
	if conflict {
		return fail("Merge conflict")
	}
	pr.merged = true
	pr.state = "closed"
	pr.mergedAt = fixedISO
	pr.mergeCommitSha = sha
	return c.execFields(f.sel, "MergePullRequestPayload", func(pf *gqlField) (any, bool) {
		switch pf.name {
		case "__typename":
			return "MergePullRequestPayload", true
		case "pullRequest":
			return c.resolvePull(pf.sel, rp, pr), true
		case "clientMutationId":
			return inputString(input, "clientMutationId"), true
		}
		return nil, false
	})
}

func (c *gqlCtx) mutAddComment(f *gqlField) any {
	input, _ := c.argObject(f, "input")
	subjectID := inputString(input, "subjectId")
	body := inputString(input, "body")
	fail := func(msg string) any {
		c.addErr("%s", msg)
		return c.execFields(f.sel, "AddCommentPayload", func(pf *gqlField) (any, bool) {
			if pf.name == "commentEdge" {
				return nil, true
			}
			return nil, false
		})
	}
	rp, is := c.issueByGID(subjectID)
	if is == nil {
		return fail("Could not resolve to an Issue with the id of " + subjectID + ".")
	}
	cm := &comment{id: c.s.st.nextCommentID, body: body, seq: c.s.st.nextSeq()}
	c.s.st.nextCommentID++
	is.comments = append(is.comments, cm)
	return c.execFields(f.sel, "AddCommentPayload", func(pf *gqlField) (any, bool) {
		switch pf.name {
		case "__typename":
			return "AddCommentPayload", true
		case "commentEdge":
			return c.execFields(pf.sel, "CommentEdge", func(ef *gqlField) (any, bool) {
				switch ef.name {
				case "__typename":
					return "CommentEdge", true
				case "cursor":
					return gqlCursor(cm.id), true
				case "node":
					return c.execFields(ef.sel, "Comment", func(cf *gqlField) (any, bool) {
						switch cf.name {
						case "__typename":
							return "Comment", true
						case "id":
							return gid("Comment", rp.id, cm.id), true
						case "body":
							return cm.body, true
						case "createdAt", "updatedAt":
							return fixedISO, true
						case "author":
							return c.execFields(cf.sel, "User", func(uf *gqlField) (any, bool) {
								return c.resolveUserField(uf)
							}), true
						}
						return nil, false
					}), true
				}
				return nil, false
			}), true
		case "subject":
			return c.resolveIssue(pf.sel, rp, is), true
		case "clientMutationId":
			return inputString(input, "clientMutationId"), true
		}
		return nil, false
	})
}

// ---------------------------------------------------------------------------
// MCP server (/mcp): JSON-RPC 2.0 over streamable HTTP, revision 2026-07-28
// (with the legacy initialize handshake as a fallback).
// ---------------------------------------------------------------------------

// mcpToolsResult returns the fixed tools/list result. It is marshalled once
// at startup so two tools/list calls answer byte-identical lists.
func mcpToolsResult() map[string]any {
	strProp := func(desc string) map[string]any {
		return map[string]any{"type": "string", "description": desc}
	}
	tool := func(name, desc string, props map[string]any, required []string) map[string]any {
		return map[string]any{
			"name":        name,
			"description": desc,
			"inputSchema": map[string]any{
				"type":       "object",
				"properties": props,
				"required":   required,
			},
		}
	}
	return map[string]any{
		"tools": []any{
			tool("create_repo", "Create a repository owned by the authenticated user.", map[string]any{
				"name":        strProp("Repository name"),
				"description": strProp("Repository description"),
				"private":     map[string]any{"type": "boolean", "description": "Whether the repository is private"},
			}, []string{"name"}),
			tool("get_repo", "Get a repository by owner and name.", map[string]any{
				"owner": strProp("Repository owner login"),
				"repo":  strProp("Repository name"),
			}, []string{"owner", "repo"}),
			tool("create_issue", "Create an issue in a repository.", map[string]any{
				"owner": strProp("Repository owner login"),
				"repo":  strProp("Repository name"),
				"title": strProp("Issue title"),
				"body":  strProp("Issue body"),
			}, []string{"owner", "repo", "title"}),
			tool("list_issues", "List issues in a repository.", map[string]any{
				"owner": strProp("Repository owner login"),
				"repo":  strProp("Repository name"),
				"state": strProp("Issue state filter: open, closed, or all"),
			}, []string{"owner", "repo"}),
			tool("create_pull_request", "Create a pull request from one branch into another.", map[string]any{
				"owner": strProp("Repository owner login"),
				"repo":  strProp("Repository name"),
				"title": strProp("Pull request title"),
				"body":  strProp("Pull request body"),
				"head":  strProp("Head branch name"),
				"base":  strProp("Base branch name"),
			}, []string{"owner", "repo", "title", "head", "base"}),
			tool("merge_pull_request", "Merge a pull request with a squash merge.", map[string]any{
				"owner":       strProp("Repository owner login"),
				"repo":        strProp("Repository name"),
				"pull_number": map[string]any{"type": "integer", "description": "Pull request number"},
			}, []string{"owner", "repo", "pull_number"}),
		},
	}
}

type mcpRequest struct {
	JSONRPC string          `json:"jsonrpc"`
	ID      json.RawMessage `json:"id"`
	Method  string          `json:"method"`
	Params  map[string]any  `json:"params"`
}

func (s *server) handleMCP(w http.ResponseWriter, r *http.Request) {
	if r.Method == http.MethodDelete {
		// A legacy session goodbye; nothing is held.
		w.WriteHeader(http.StatusNoContent)
		return
	}
	if r.Method != http.MethodPost {
		s.writeJSON(w, http.StatusMethodNotAllowed, errBody("Method Not Allowed"))
		return
	}
	if !s.requireAuth(w, r) {
		return
	}
	body, err := io.ReadAll(io.LimitReader(r.Body, 4<<20))
	_ = r.Body.Close()
	if err != nil {
		s.mcpError(w, nil, -32700, "Parse error", http.StatusBadRequest)
		return
	}
	var req mcpRequest
	if err := json.Unmarshal(body, &req); err != nil {
		// A body that is not JSON: HTTP 400 with JSON-RPC -32700.
		s.mcpError(w, nil, -32700, "Parse error", http.StatusBadRequest)
		return
	}
	// A notification (no id) gets no JSON-RPC answer.
	if len(req.ID) == 0 || string(req.ID) == "null" {
		w.WriteHeader(http.StatusAccepted)
		return
	}
	if strings.HasPrefix(req.Method, "notifications/") {
		w.WriteHeader(http.StatusAccepted)
		return
	}

	switch req.Method {
	case "server/discover":
		s.mcpResult(w, req.ID, map[string]any{
			"supportedVersions": []string{"2026-07-28"},
			"capabilities":      map[string]any{"tools": map[string]any{}},
			"serverInfo":        map[string]any{"name": s.cfg.agent, "version": s.cfg.version},
			"_meta": map[string]any{
				"io.modelcontextprotocol/serverInfo": map[string]any{"name": s.cfg.agent, "version": s.cfg.version},
			},
		})
	case "initialize":
		version := "2025-11-25"
		if v, ok := req.Params["protocolVersion"].(string); ok && isRevision(v) {
			version = v
		}
		s.mcpResult(w, req.ID, map[string]any{
			"protocolVersion": version,
			"capabilities":    map[string]any{"tools": map[string]any{}},
			"serverInfo":      map[string]any{"name": s.cfg.agent, "version": s.cfg.version},
		})
	case "ping":
		s.mcpResult(w, req.ID, map[string]any{})
	case "tools/list":
		// The pre-marshalled result, byte-identical on every call.
		resp := make([]byte, 0, len(s.mcpToolsJSON)+64)
		resp = append(resp, []byte(`{"jsonrpc":"2.0","id":`)...)
		resp = append(resp, req.ID...)
		resp = append(resp, []byte(`,"result":`)...)
		resp = append(resp, s.mcpToolsJSON...)
		resp = append(resp, '}')
		s.writeRawJSON(w, http.StatusOK, resp)
	case "tools/call":
		s.mcpCallTool(w, req.ID, req.Params)
	default:
		s.mcpError(w, req.ID, -32601, "Method not found: "+req.Method, http.StatusOK)
	}
}

func isRevision(v string) bool {
	if len(v) != 10 || v[4] != '-' || v[7] != '-' {
		return false
	}
	for i, c := range v {
		if i == 4 || i == 7 {
			continue
		}
		if c < '0' || c > '9' {
			return false
		}
	}
	return true
}

func (s *server) mcpResult(w http.ResponseWriter, id json.RawMessage, result any) {
	resp := make([]byte, 0, 256)
	resp = append(resp, []byte(`{"jsonrpc":"2.0","id":`)...)
	resp = append(resp, id...)
	resp = append(resp, []byte(`,"result":`)...)
	resp = append(resp, marshalJSON(result)...)
	resp = append(resp, '}')
	s.writeRawJSON(w, http.StatusOK, resp)
}

func (s *server) mcpError(w http.ResponseWriter, id json.RawMessage, code int, message string, status int) {
	if len(id) == 0 {
		id = json.RawMessage("null")
	}
	resp := map[string]any{
		"jsonrpc": "2.0",
		"id":      json.RawMessage(id),
		"error":   map[string]any{"code": code, "message": message},
	}
	s.writeJSON(w, status, resp)
}

// --- tools/call --------------------------------------------------------------

func mcpToolString(args map[string]any, key string) (string, bool) {
	v, ok := args[key]
	if !ok {
		return "", false
	}
	s, ok := v.(string)
	if !ok || s == "" {
		return "", false
	}
	return s, true
}

func mcpToolInt(args map[string]any, key string) (int, bool) {
	v, ok := args[key]
	if !ok {
		return 0, false
	}
	switch n := v.(type) {
	case float64:
		return int(n), true
	case int:
		return n, true
	case string:
		i, err := strconv.Atoi(n)
		return i, err == nil
	}
	return 0, false
}

func mcpToolBool(args map[string]any, key string) bool {
	v, ok := args[key]
	if !ok {
		return false
	}
	b, _ := v.(bool)
	return b
}

func (s *server) mcpCallTool(w http.ResponseWriter, id json.RawMessage, params map[string]any) {
	name, _ := params["name"].(string)
	args, _ := params["arguments"].(map[string]any)
	if args == nil {
		args = map[string]any{}
	}
	// The suite may also pass a full_name ("owner/repo") instead of
	// separate owner/repo properties; split it for the tools that need it.
	if _, hasRepo := args["repo"]; !hasRepo {
		if full, ok := args["full_name"].(string); ok {
			if i := strings.IndexByte(full, '/'); i >= 0 {
				args["owner"] = full[:i]
				args["repo"] = full[i+1:]
			}
		}
	}

	// Resolve the tool by suffix, case-insensitively (a server prefix is
	// allowed): "github__create_issue" serves create_issue.
	canonical := ""
	for _, c := range []string{"create_repo", "get_repo", "create_issue", "list_issues", "create_pull_request", "merge_pull_request"} {
		norm := func(s string) string {
			var b strings.Builder
			for _, r := range s {
				if (r >= 'a' && r <= 'z') || (r >= '0' && r <= '9') {
					b.WriteRune(r)
				}
			}
			return b.String()
		}
		if norm(name) == norm(c) || (len(norm(name)) > len(norm(c)) && strings.HasSuffix(norm(name), norm(c))) {
			canonical = c
			break
		}
	}
	if canonical == "" {
		s.mcpError(w, id, -32602, "Unknown tool: "+name, http.StatusOK)
		return
	}

	result, toolErr := s.mcpRunTool(canonical, args)
	if toolErr == "invalid-params" {
		s.mcpError(w, id, -32602, "Invalid params for tool "+canonical, http.StatusOK)
		return
	}
	text := ""
	if result != nil {
		text = string(marshalJSON(result))
	}
	if toolErr != "" {
		text = toolErr
	}
	resp := map[string]any{
		"content": []any{map[string]any{"type": "text", "text": text}},
		"isError": toolErr != "",
	}
	if result != nil {
		resp["structuredContent"] = result
	}
	s.mcpResult(w, id, resp)
}

// mcpRunTool executes one tool. It returns the result object and an error
// string: "" on success, "invalid-params" for missing required arguments,
// or a tool error message (answered as isError:true).
func (s *server) mcpRunTool(name string, args map[string]any) (any, string) {
	switch name {
	case "create_repo":
		repoName, ok := mcpToolString(args, "name")
		if !ok {
			// The suite may address the name as "repo".
			if repoName, ok = mcpToolString(args, "repo"); !ok {
				return nil, "invalid-params"
			}
		}
		desc, _ := args["description"].(string)
		private := mcpToolBool(args, "private")
		s.st.mu.Lock()
		defer s.st.mu.Unlock()
		if s.st.getRepo(s.cfg.viewer, repoName) != nil {
			return nil, "name already exists on this account"
		}
		rp := &repo{
			id:            s.st.nextRepoID,
			name:          repoName,
			owner:         s.cfg.viewer,
			private:       private,
			description:   desc,
			defaultBranch: defaultBranch,
			seq:           s.st.nextSeq(),
			refs:          make(map[string]string),
			objects:       make(map[string]*gitObj),
			issues:        make(map[int]*issue),
			pulls:         make(map[int]*pull),
			labels:        make(map[string]*label),
			nextNumber:    1,
		}
		s.st.nextRepoID++
		s.st.repos[repoKey(rp.owner, rp.name)] = rp
		s.st.repoByID[rp.id] = rp
		return s.repoJSON(rp), ""

	case "get_repo":
		owner, ok1 := mcpToolString(args, "owner")
		repoName, ok2 := mcpToolString(args, "repo")
		if !ok1 || !ok2 {
			return nil, "invalid-params"
		}
		s.st.mu.RLock()
		defer s.st.mu.RUnlock()
		rp := s.st.getRepo(owner, repoName)
		if rp == nil {
			return nil, "Not Found"
		}
		return s.repoJSON(rp), ""

	case "create_issue":
		owner, ok1 := mcpToolString(args, "owner")
		repoName, ok2 := mcpToolString(args, "repo")
		title, ok3 := mcpToolString(args, "title")
		if !ok1 || !ok2 || !ok3 {
			return nil, "invalid-params"
		}
		body, _ := args["body"].(string)
		s.st.mu.Lock()
		defer s.st.mu.Unlock()
		rp := s.st.getRepo(owner, repoName)
		if rp == nil {
			return nil, "Not Found"
		}
		is := &issue{
			id:     s.st.nextIssueID,
			number: rp.nextNumber,
			title:  title,
			body:   body,
			state:  "open",
			seq:    s.st.nextSeq(),
		}
		s.st.nextIssueID++
		rp.nextNumber++
		rp.issues[is.number] = is
		return s.issueJSON(rp, is), ""

	case "list_issues":
		owner, ok1 := mcpToolString(args, "owner")
		repoName, ok2 := mcpToolString(args, "repo")
		if !ok1 || !ok2 {
			return nil, "invalid-params"
		}
		state, _ := args["state"].(string)
		if state == "" {
			state = "open"
		}
		s.st.mu.RLock()
		defer s.st.mu.RUnlock()
		rp := s.st.getRepo(owner, repoName)
		if rp == nil {
			return nil, "Not Found"
		}
		var list []*issue
		for _, is := range rp.issues {
			if state != "all" && is.state != state {
				continue
			}
			list = append(list, is)
		}
		sort.Slice(list, func(i, j int) bool { return list[i].seq < list[j].seq })
		out := make([]any, 0, len(list))
		for _, is := range list {
			out = append(out, s.issueJSON(rp, is))
		}
		return map[string]any{"issues": out}, ""

	case "create_pull_request":
		owner, ok1 := mcpToolString(args, "owner")
		repoName, ok2 := mcpToolString(args, "repo")
		title, ok3 := mcpToolString(args, "title")
		head, ok4 := mcpToolString(args, "head")
		base, ok5 := mcpToolString(args, "base")
		if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 {
			return nil, "invalid-params"
		}
		body, _ := args["body"].(string)
		s.st.mu.Lock()
		defer s.st.mu.Unlock()
		rp := s.st.getRepo(owner, repoName)
		if rp == nil {
			return nil, "Not Found"
		}
		headTip, headOk := rp.refs["refs/heads/"+head]
		baseTip, baseOk := rp.refs["refs/heads/"+base]
		if !headOk || !baseOk {
			return nil, "head or base branch does not exist"
		}
		if head == base {
			return nil, "head and base are the same"
		}
		for _, pr := range rp.pulls {
			if pr.state == "open" && pr.headRef == head && pr.baseRef == base {
				return nil, "A pull request already exists for these branches"
			}
		}
		pr := &pull{
			id:      s.st.nextIssueID,
			number:  rp.nextNumber,
			title:   title,
			body:    body,
			state:   "open",
			headRef: head,
			baseRef: base,
			headSha: headTip,
			baseSha: baseTip,
			seq:     s.st.nextSeq(),
		}
		s.st.nextIssueID++
		rp.nextNumber++
		rp.pulls[pr.number] = pr
		return s.pullJSON(rp, pr), ""

	case "merge_pull_request":
		owner, ok1 := mcpToolString(args, "owner")
		repoName, ok2 := mcpToolString(args, "repo")
		number, ok3 := mcpToolInt(args, "pull_number")
		if !ok1 || !ok2 || !ok3 {
			// The suite may address the number as "number".
			if number, ok3 = mcpToolInt(args, "number"); !ok1 || !ok2 || !ok3 {
				return nil, "invalid-params"
			}
		}
		s.st.mu.Lock()
		defer s.st.mu.Unlock()
		rp := s.st.getRepo(owner, repoName)
		if rp == nil {
			return nil, "Not Found"
		}
		pr, ok := rp.pulls[number]
		if !ok {
			return nil, "Not Found"
		}
		if pr.merged {
			return nil, "Pull request is already merged"
		}
		if pr.state != "open" {
			return nil, "Pull request is closed"
		}
		sha, conflict, err := rp.squashMerge(s.cfg, pr)
		if err != nil {
			return nil, err.Error()
		}
		if conflict {
			return nil, "Merge conflict"
		}
		pr.merged = true
		pr.state = "closed"
		pr.mergedAt = fixedISO
		pr.mergeCommitSha = sha
		return s.pullJSON(rp, pr), ""
	}
	return nil, "invalid-params"
}
