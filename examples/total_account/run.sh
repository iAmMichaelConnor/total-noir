#!/usr/bin/env bash
# Compile TotalAccount, run its unit tests, lint its functions, and run its
# TXE tests (which also deploy the MultiCall test contract in
# ../total_account_multicall).
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

nargo compile --silence-warnings
artifact=target/total_account-TotalAccount.json

# Unit tests of the pure logic need no oracle.
nargo test --silence-warnings ecies::
nargo test --silence-warnings signing_key::

fns=()
for fn in constructor encrypt_for_owner entrypoint verify_private_authwit; do
  fns+=(--function "$fn")
done
echo "== total-lint"
# aztec-nr's own items (the private-function prologue, its oracles and
# hints) are accepted by total-lint-baseline.json; any other unjustified
# item fails the run. After reviewing a change, rewrite the baseline by
# running this command with --write-baseline instead of --baseline.
"$lint" "$artifact" --summary "${fns[@]}" \
  --lib-src "$root/noir/total/src/" \
  --allow-src "$here/src" --allow-src "$root/noir/total_aztec/src" \
  --allow-entry-ranges --baseline "$here/total-lint-baseline.json"

if txe_enabled; then
  (cd ../total_account_multicall && nargo compile --silence-warnings)
  for a in "$artifact" ../total_account_multicall/target/multicall-MultiCall.json; do
    bb aztec_process -i "$a" >/dev/null
  done
  txe_start
  nargo test --silence-warnings --oracle-resolver "$txe_url" --test-threads 1 test::
fi
