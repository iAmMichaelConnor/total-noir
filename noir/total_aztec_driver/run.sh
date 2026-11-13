#!/usr/bin/env bash
# Compile TotalAztecDriver, lint every driver function, and run its TXE
# tests. The library's own unit tests run in noir/total_aztec (`nargo test`).
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
artifact=target/total_aztec_driver-TotalAztecDriver.json
fns=()
for fn in read_immutable read_single read_mutable read_set read_at read_byte \
  read_from_witness note_exists key_usable initialized public_immutable_initialized \
  read_public_immutable read_delayed consume_with_proof relay_consume set_key \
  try_set_key; do
  fns+=(--function "$fn")
done
echo "== total-lint"
# aztec-nr's own items (the private-function prologue, its oracles and
# hints) are accepted by total-lint-baseline.json; any other unjustified
# item fails the run. After reviewing a change, rewrite the baseline by
# running this command with --write-baseline instead of --baseline.
"$lint" "$artifact" --summary "${fns[@]}" --lib-src "$root/noir/total/src/" \
  --allow-src "$here/src" --allow-src "$root/noir/total_aztec/src" \
  --allow-entry-ranges --baseline "$here/total-lint-baseline.json"

# Uses of the library outside what it can make total: each must fail the
# lint (exit code 1) against the same baseline, because the library's own
# markers no longer justify what depends on the caller.
for fn in set_key_for unmarked_refuse unmarked_pin unmarked_consume read_bool_immutable; do
  status=0
  "$lint" "$artifact" --function "$fn" --lib-src "$root/noir/total/src/" \
    --allow-src "$here/src" --allow-src "$root/noir/total_aztec/src" \
    --allow-entry-ranges --baseline "$here/total-lint-baseline.json" >/dev/null || status=$?
  if [[ $status != 1 ]]; then
    echo "total-lint: expected $fn to be reported (exit 1), got exit $status" >&2
    exit 1
  fi
  echo "total-lint reports $fn, as expected"
done

if txe_enabled; then
  bb aztec_process -i "$artifact" >/dev/null
  txe_start
  nargo test --silence-warnings --oracle-resolver "$txe_url" --test-threads 1 test::
fi
