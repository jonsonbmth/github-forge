// Thin launcher for the forge: the entry point the trial runtime starts
// (`node /bot/main.ts`). It execs the statically linked Go binary committed
// next to it and forwards the exit code. All of the forge — git smart HTTP,
// REST v3, GraphQL, MCP — lives in main.go; this file only starts it.
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

const here = dirname(fileURLToPath(import.meta.url));
const binary = join(here, 'forge');

const child = spawn(binary, process.argv.slice(2), {
  stdio: 'inherit',
  env: process.env,
});

child.on('error', (err) => {
  console.error(`failed to start ${binary}: ${err.message}`);
  process.exit(1);
});

child.on('exit', (code, signal) => {
  if (signal) {
    process.kill(process.pid, signal);
    return;
  }
  process.exit(code ?? 1);
});
