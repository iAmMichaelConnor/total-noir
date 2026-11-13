#!/usr/bin/env bash
# Check that total's hints stay runnable in co-noir's MPC witness extension.
# Compiles lint/fixtures/co_noir_hints, which calls the library's hint-using
# entries, and runs `total-lint --brillig-ops` on it: exit 1 if its Brillig
# holds an opcode co-noir's MPC Brillig VM cannot execute (integer And, Or,
# Xor, Shl, Shr, ConditionalMov, a black box other than ToRadix). With CO_NOIR
# set it then runs the fixture through co-noir itself: split-input and a
# three-party REP3 generate-witness on localhost, and checks that the witness
# extension succeeds.
#
# Circuit authors targeting co-noir run the same report on their own artifact:
# scripts/total-lint.sh <artifact.json> --brillig-ops
#
# Needs nargo on PATH (1.0.0-rc.3 or 1.0.0; co-noir at the pinned fork
# reads nargo 1.0.0 artifacts). Optional environment:
#   CO_NOIR     co-noir binary, built from the main branch of
#               github.com/iAmMichaelConnor/co-snarks; enables the MPC run
#   CO_SNARKS   co-snarks checkout whose co-noir/co-noir/examples/data holds
#               the example TLS keys (default: the directory three levels
#               above CO_NOIR's target/release)
#   CO_NOIR_PORT first of three localhost ports (default 21510)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
fixture=$root/lint/fixtures/co_noir_hints
work=$(mktemp -d)
export TMPDIR="$work"
trap 'rm -rf "$work"' EXIT

cp -r "$fixture/src" "$fixture/Nargo.toml" "$fixture/Prover.toml" "$work/"
sed -i "s#path = \"../../../noir/total\"#path = \"$root/noir/total\"#" "$work/Nargo.toml"
(cd "$work" && nargo execute --silence-warnings >/dev/null)
artifact=$work/target/co_noir_hints.json
"$root/scripts/total-lint.sh" "$artifact" --brillig-ops --summary

[[ -n ${CO_NOIR:-} ]] || exit 0
CO_SNARKS=${CO_SNARKS:-$(cd "$(dirname "$CO_NOIR")/../.." && pwd)}
data=$CO_SNARKS/co-noir/co-noir/examples/data
port=${CO_NOIR_PORT:-21510}
mkdir -p "$work/net"
ln -s "$data" "$work/net/data"
for i in 0 1 2; do
  {
    printf '[network]\nmy_id = %d\nbind_addr = "127.0.0.1:%d"\n\n' "$i" $((port + i))
    for j in 0 1 2; do printf '[[network.parties]]\nid = %d\ndns_name = "127.0.0.1:%d"\n\n' "$j" $((port + j)); done
    printf '[network.tls]\nkey = "data/key%d.der"\ncerts = ["data/cert0.der", "data/cert1.der", "data/cert2.der"]\n' "$i"
  } > "$work/net/party$i.toml"
done
cd "$work/net"
mkdir -p "$work/shares"
"$CO_NOIR" split-input --circuit "$artifact" --input "$work/Prover.toml" --protocol REP3 --out-dir "$work/shares" >/dev/null
pids=()
for i in 0 1 2; do
  "$CO_NOIR" generate-witness --input "$work/shares/Prover.toml.$i.shared" --circuit "$artifact" \
    --protocol REP3 --config "party$i.toml" --out "$work/shares/witness.$i.shared" > "$work/party$i.log" 2>&1 &
  pids+=($!)
done
status=0
for p in "${pids[@]}"; do wait "$p" || status=1; done
if [[ $status != 0 ]]; then
  for i in 0 1 2; do echo "--- party $i"; tail -20 "$work/party$i.log"; done
  echo "co-noir witness extension FAILED"
  exit 1
fi
echo "co-noir witness extension (REP3, 3 parties): ok"
