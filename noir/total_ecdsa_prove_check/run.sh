#!/usr/bin/env bash
# Execute total_ecdsa_prove_check on each Prover*.toml, then prove and
# verify each witness with bb (UltraHonk): the ECDSA entries must give the
# expected verdict and a valid proof on inputs that bb's ECDSA gadgets
# cannot prove when they reach them directly. Needs nargo 1.0.0-rc.3 and
# bb 6.0.0 on PATH (BB overrides the bb binary).
set -euo pipefail
cd "$(dirname "$0")"
bb=${BB:-bb}
# The entries' totality argument is about one bb version
# (docs/ecdsa-totality.md): refuse any other, so that a version bump cannot
# pass this check without the argument being redone (CONTRIBUTING.md,
# "Bumping bb").
proved_for=6.0.0
have=$("$bb" --version 2>/dev/null | head -1)
if [[ $have != "$proved_for" ]]; then
  echo "bb is $have; the ECDSA totality argument is for bb $proved_for (docs/ecdsa-totality.md)" >&2
  exit 1
fi
# work files under the package's target directory (no system temp directory)
work=$PWD/target/prove-check.$$
mkdir -p "$work"
export TMPDIR=$work
trap 'rm -rf "$work"' EXIT

nargo compile --silence-warnings
"$bb" write_vk -b target/total_ecdsa_prove_check.json -o "$work" > "$work/vk.log" 2>&1 ||
  { cat "$work/vk.log"; exit 1; }
for p in Prover*.toml; do
  name=${p%.toml}
  echo "== $name"
  nargo execute --silence-warnings -p "$p" "$name"
  mkdir -p "$work/$name"
  "$bb" prove -b target/total_ecdsa_prove_check.json -w "target/$name.gz" -k "$work/vk" -o "$work/$name" \
    > "$work/$name.log" 2>&1 || { tail -5 "$work/$name.log"; echo "bb prove failed on $name"; exit 1; }
  "$bb" verify -k "$work/vk" -p "$work/$name/proof" -i "$work/$name/public_inputs" 2>&1 | tail -1
done
