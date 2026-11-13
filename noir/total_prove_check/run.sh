#!/usr/bin/env bash
# Execute total_prove_check on each Prover*.toml, then prove and verify
# each witness with bb (UltraHonk): the entries built on the MSM black box
# must give the right answer and a valid proof on inputs that bb's MSM
# gadget cannot prove when they reach it directly. Needs nargo 1.0.0-rc.3
# and bb 6.0.0 on PATH (BB overrides the bb binary).
set -euo pipefail
cd "$(dirname "$0")"
bb=${BB:-bb}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

nargo compile --silence-warnings
"$bb" write_vk -b target/total_prove_check.json -o "$work" > "$work/vk.log" 2>&1 ||
  { cat "$work/vk.log"; exit 1; }
for p in Prover*.toml; do
  name=${p%.toml}
  echo "== $name"
  nargo execute --silence-warnings -p "$p" "$name"
  mkdir -p "$work/$name"
  "$bb" prove -b target/total_prove_check.json -w "target/$name.gz" -k "$work/vk" -o "$work/$name" \
    > "$work/$name.log" 2>&1 || { tail -5 "$work/$name.log"; echo "bb prove failed on $name"; exit 1; }
  "$bb" verify -k "$work/vk" -p "$work/$name/proof" -i "$work/$name/public_inputs" 2>&1 | tail -1
done
