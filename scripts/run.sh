#!/usr/bin/env bash
# Runs the differential tests in noir/total_oracle_tests: builds the
# TypeScript oracle server (oracle_server.ts), starts it on $PORT (8095),
# waits until it answers, runs the tests with it as nargo's oracle resolver,
# and stops it. Needs `yarn install` first. Each test is fuzzed for
# $FUZZ_TIMEOUT seconds (default 5); extra arguments go to `nargo test`, and
# $NARGO selects the nargo binary.
set -euo pipefail

export PORT=${PORT:-8095}
cd "$(dirname "$0")/.."

echo "Building TypeScript..."
yarn build

echo "Starting TypeScript RPC server..."
node dist/oracle_server.js &
TS_SERVER_PID=$!
trap 'kill $TS_SERVER_PID' EXIT

for _ in $(seq 100); do
  curl -sf "http://127.0.0.1:${PORT}/health" > /dev/null && break
  sleep 0.1
done
curl -sf "http://127.0.0.1:${PORT}/health" > /dev/null || { echo "oracle server did not start" >&2; exit 1; }

"${NARGO:-nargo}" --program-dir=noir/total_oracle_tests test \
  --oracle-resolver "http://127.0.0.1:${PORT}" --fuzz-timeout "${FUZZ_TIMEOUT:-5}" "$@"
