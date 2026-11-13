#!/usr/bin/env bash
# The proof-of-nullification example: compile and test the owner circuit,
# check that the executor contract pins its vk (make_fixture.py --vk),
# compile and lint the executor contract, and, with the TXE, play the
# whole exchange: the TXE prints the planted note's values, the owner's
# pin, the executors' addresses and the executor's anchor block, the
# owner proves unbound and bound handoffs with bb and the executor runs
# its pre-check on each (make_fixture.py, which writes the proofs to
# target/fixture/), the TXE tests stage handoffs and consume the note,
# and bb proves the executor's binding flags and recursive check on the
# real proofs (outer_check.py). Nothing under src/ is generated: after
# changing the owner circuit, run `python3 make_fixture.py --vk --update`
# to rewrite the vk pin and executor/src/owner_vk.nr.
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

echo "== prove_nullification: test, compile, gates"
(cd prove_nullification && nargo test --silence-warnings && nargo compile --silence-warnings)
bb gates -t noir-recursive -b prove_nullification/target/prove_nullification.json | grep circuit_size
echo "== owner circuit vk: pinned by the executor, copied in executor/src/owner_vk.nr"
python3 -I make_fixture.py --vk

echo "== executor: compile, lint"
(cd executor && nargo compile --silence-warnings)
artifact=executor/target/nullification_executor-NullificationExecutor.json
echo "== total-lint consume, register"
# aztec-nr's own items are accepted by total-lint-baseline.json; any other
# unjustified item fails the run (rewrite it with --write-baseline after
# reviewing a change).
"$lint" "$artifact" --summary --function consume --function register \
  --lib-src "$root/noir/total/src/" \
  --allow-src "$here/executor/src" --allow-src "$root/noir/total_aztec/src" \
  --allow-entry-ranges --baseline "$here/total-lint-baseline.json"

if txe_enabled; then
  bb aztec_process -i "$artifact" >/dev/null
  txe_start
  echo "== TXE fixture values, owner proof, executor pre-check"
  (cd executor && nargo test --silence-warnings --oracle-resolver "$txe_url" \
    --show-output fixture_values) > "$work/fixture.txt"
  python3 -I make_fixture.py "$work/fixture.txt" "$work/owner"
  echo "== TXE tests"
  (cd executor && nargo test --silence-warnings --oracle-resolver "$txe_url" \
    --test-threads 1 test::)
fi

echo "== executor_outer: compile"
(cd executor_outer && nargo compile --silence-warnings)
if txe_enabled; then
  echo "== executor_outer: bb prove and verify on the owner's proofs"
  python3 -I outer_check.py "$work/outer"
fi
