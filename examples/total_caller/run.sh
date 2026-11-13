#!/usr/bin/env bash
# Compile Caller, GriefAccount, ShortAccount and TotalAccount, lint
# Caller.seal_to, and run the TXE tests.
#
# Needs nargo 1.0.0-rc.3, bb 6.0.0 and python3 on PATH; the TXE settings are
# in scripts/txe.sh. TOTAL_LINT selects another total-lint binary (default:
# built from this checkout by scripts/total-lint.sh).
set -euo pipefail
cd "$(dirname "$0")"
here=$(pwd)
root=$(cd ../.. && pwd)
lint=$root/scripts/total-lint.sh
"$lint" --help >/dev/null  # build it now, so a build failure stops the run
source "$root/scripts/txe.sh"

(cd ../total_account && nargo compile --silence-warnings)
nargo compile --silence-warnings

echo "== total-lint seal_to"
# aztec-nr's own items are accepted by total-lint-baseline.json; any other
# unjustified item fails the run (rewrite it with --write-baseline after
# reviewing a change).
"$lint" target/caller-Caller.json --summary --function seal_to \
  --lib-src "$root/noir/total/src/" --allow-src "$here/caller/src" \
  --allow-src "$root/noir/total_aztec/src" \
  --allow-entry-ranges --baseline "$here/total-lint-baseline.json"

if txe_enabled; then
  for a in ../total_account/target/total_account-TotalAccount.json target/grief_account-GriefAccount.json \
    target/short_account-ShortAccount.json target/caller-Caller.json; do
    bb aztec_process -i "$a" >/dev/null
  done
  txe_start
  nargo test --silence-warnings --oracle-resolver "$txe_url" --test-threads 1 test::
fi
