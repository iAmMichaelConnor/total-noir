#!/usr/bin/env bash
# Measure gate costs of total primitives against native forms.
# Writes build/gate-costs.md. Builds go to build/gate-bench
# (gitignored, deleted when the run finishes).
#
# Usage: scripts/gate-bench.sh [--groups G,...] [--only ID,...] [--smoke]
# (scripts/gate_bench.py --help lists every option)
set -euo pipefail
cd "$(dirname "$0")/.."
exec nice -n 19 python3 -I scripts/gate_bench.py "$@"
