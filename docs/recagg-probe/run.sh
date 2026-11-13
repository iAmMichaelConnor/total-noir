#!/usr/bin/env bash
# Predication probe for RecursiveAggregation (std::verify_proof_with_type)
# on nargo 1.0.0-rc.3 and bb 6.0.0. Makes a real ZK UltraHonk proof of the
# tiny `inner` circuit, then runs `outer` (the verification under
# `if present`) and `uncond` (no branch) through nargo execute, bb prove
# and bb verify for each case, and prints one line per case. Every outer
# proof is verified against the vk of the present = true, valid case: the
# circuit (and its vk) does not depend on the witness.
#
# Needs nargo, bb and python3 on PATH. Writes only under a scratch directory
# made with mktemp -d under ${TXE_TMP_ROOT:-${TMPDIR:-/tmp}}, deleted on exit.
set -uo pipefail
cd "$(dirname "$0")"
here=$(pwd)
TXE_TMP_ROOT=${TXE_TMP_ROOT:-${TMPDIR:-/tmp}}
mkdir -p "$TXE_TMP_ROOT"
work=$(mktemp -d "$TXE_TMP_ROOT/recagg.XXXXXX")
export TMPDIR=$work
trap 'rm -rf "$work"; rm -rf "$here"/*/target' EXIT

(cd inner && nargo execute --silence-warnings w >/dev/null) || exit 1
bb prove -t noir-recursive --output_format json --write_vk -b inner/target/inner.json \
  -w inner/target/w.gz -o "$work/inner" >/dev/null 2>&1 || { echo "inner proof failed"; exit 1; }
echo "inner: ZK UltraHonk proof, $(python3 -c "import json;print(len(json.load(open('$work/inner/vk.json'))['vk']))") vk fields, $(python3 -c "import json;print(len(json.load(open('$work/inner/proof.json'))['proof']))") proof fields"
for pkg in outer uncond; do
  (cd $pkg && nargo compile --silence-warnings --print-acir) | grep -o 'RECURSIVE_AGGREGATION.*' | sed -E 's/\[w[0-9]+(, w[0-9]+)+\]/[...]/g' | sed "s/^/$pkg ACIR: /"
done

case_line() {  # pkg case [vk-for-verify]
  local pkg=$1 c=$2 d="$work/$1-$2" toml="$work/$1-$2.toml"
  python3 -I mk_prover.py "$work/inner" "$c" "$toml"
  [[ $pkg == uncond ]] && sed -i '/^present/d' "$toml"
  local ex pr ve
  if (cd $pkg && nargo execute --silence-warnings -p "$toml" "w_$c" >/dev/null 2>&1); then ex=ok; else ex=FAILS; fi
  pr=-; ve=-
  if [[ $ex == ok ]]; then
    if bb prove -t noir-recursive --output_format json --write_vk -b $pkg/target/$pkg.json \
      -w $pkg/target/w_$c.gz -o "$d" >"$d.log" 2>&1; then
      pr=ok
      bb verify -t noir-recursive -k "${3:-$d}/vk.json" -p "$d/proof.json" -i "$d/public_inputs.json" \
        >/dev/null 2>&1 && ve=ok || ve=FAILS
    else
      pr="FAILS ($(grep -E 'Assertion failed|Failed to verify|VK Hash|canonical' "$d.log" | head -1 | cut -c1-70))"
    fi
  fi
  printf '%-7s %-16s execute %-5s prove %s verify %s\n' "$pkg" "$c" "$ex" "$pr" "$ve"
}
case_line outer true-valid
for c in false-garbage false-zero false-valid true-garbage true-zero true-tampered true-wrongpi true-wronghash; do
  case_line outer $c "$work/outer-true-valid"
done
case_line uncond true-valid
case_line uncond true-garbage
bb gates -t noir-recursive -b outer/target/outer.json 2>/dev/null | grep circuit_size | sed 's/^ */outer gates: /'
