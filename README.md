# github-forge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/jonsonbmth/github-forge/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/jonsonbmth/github-forge/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A GitHub-compatible git forge in a single Go file (`main.go`, standard library
only), served by one static binary. Four surfaces over one shared store: git
smart HTTP (protocol v0 and v2, clone/fetch/push with pack read/write, shallow
and incremental fetch, fast-forward-only receive-pack), REST v3
(repos/branches/commits/contents/labels/issues/pulls, pagination, squash
merge with conflict detection), GraphQL (viewer, repository, issues,
pullRequests, Relay-style global ids and cursor pagination, mutations,
introspection), and an MCP server (Streamable HTTP, `server/discover`,
`initialize`, `tools/list`, `tools/call` for six tools). Bearer-token auth,
in-memory store, fixed timestamps for deterministic exports.

## Run it

```sh
# Trial mode (the way make.fun runs it): node main.ts spawns ./forge,
# which binds an ephemeral port, registers with $MAKEFUN_ENV_URL and exits
# when the environment reports done.
node main.ts

# Standalone, for local testing:
MAKEFUN_SHOP_TOKEN=dev-token PORT=8080 ./forge
```

Build the binary from source with Go 1.25:

```sh
CGO_ENABLED=0 go build -ldflags="-s -w" -trimpath -o forge main.go
```

Local conformance (120/120 checks) and benchmarks are run with the kit's
runner against a running forge:

```sh
node --experimental-strip-types sdk/run.ts --url http://127.0.0.1:8080 --token dev-token --perf --json
```

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
