#!/usr/bin/env bash
# Execute total_witness_check on each Prover*.toml: total's entries on
# solver-time witnesses, asserted against unconstrained references, and the
# BoundedVec forms on lengths above MaxLen. Needs nargo 1.0.0-rc.3 or later.
set -euo pipefail
cd "$(dirname "$0")"
for p in Prover*.toml; do
  echo "== ${p%.toml}"
  nargo execute --silence-warnings -p "$p"
done
