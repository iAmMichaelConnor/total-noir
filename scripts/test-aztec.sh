#!/usr/bin/env bash
# Tests of everything built on aztec-nr: total_aztec's unit tests, then each
# contract's compile, lint and TXE run (scripts/txe.sh has the settings).
#
# Needs nargo 1.0.0-rc.3, bb 6.0.0, cargo, python3 and, unless SKIP_TXE=1,
# the TXE of @aztec-labs/txe 6.0.0.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)

echo "::group::noir/total_aztec"
(cd "$root/noir/total_aztec" && nargo test --silence-warnings)
echo "::endgroup::"

for script in noir/total_aztec_driver/run.sh examples/total_account/run.sh \
  examples/total_caller/run.sh examples/nullification_proof/run.sh; do
  echo "::group::$script"
  "$root/$script"
  echo "::endgroup::"
done
