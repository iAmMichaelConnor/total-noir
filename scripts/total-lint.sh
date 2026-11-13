#!/usr/bin/env bash
# Build total-lint from the sources in this checkout, then run it with the
# given arguments. No prebuilt binary ships in the tree: a binary left in
# lint/total-lint/target can be older than the sources (it classifies
# opcodes the way the commit it was built from did), so every script here
# calls the lint through this wrapper and cargo rebuilds whatever is stale.
# The build is cargo build --release --locked (Cargo.lock pins the acir
# crates at v1.0.0-rc.3); an up-to-date build costs a fraction of a second.
#
# Usage: scripts/total-lint.sh <artifact.json> [total-lint options]
# Set TOTAL_LINT to a binary to skip the build and run that binary instead.
set -euo pipefail
if [[ -z ${TOTAL_LINT:-} ]]; then
  root=$(cd "$(dirname "$0")/.." && pwd)
  cargo build --release --locked --quiet --manifest-path "$root/lint/total-lint/Cargo.toml" >&2
  TOTAL_LINT=$root/lint/total-lint/target/release/total-lint
fi
exec "$TOTAL_LINT" "$@"
