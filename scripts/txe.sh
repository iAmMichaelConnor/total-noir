# Sourced by the run.sh scripts: a scratch directory and, on request, a TXE
# server for the Aztec contract tests.
#
# Environment:
#   TXE           command that starts the TXE server of @aztec-labs/txe 6.0.0
#                 (default `txe`, from `npm install -g @aztec-labs/txe@6.0.0`)
#   SKIP_TXE      set to 1 to skip the TXE tests
#   TXE_TMP_ROOT  parent of the scratch directory (default $TMPDIR or /tmp).
#                 The TXE creates Unix sockets under the scratch directory, and
#                 a socket path longer than 107 bytes fails, so keep it short.
#
# Provides: $work (scratch, also exported as TMPDIR, deleted on exit),
# txe_enabled, and txe_start, which starts a server and sets $txe_url.

work=$(mktemp -d "${TXE_TMP_ROOT:-${TMPDIR:-/tmp}}/total-noir.XXXXXX")
export TMPDIR=$work
txe_pid=
trap '[[ -n $txe_pid ]] && kill "$txe_pid" 2>/dev/null; wait 2>/dev/null; rm -rf "$work"; true' EXIT

txe_enabled() {
  [[ ${SKIP_TXE:-0} != 1 ]]
}

txe_start() {
  local cmd=${TXE:-txe} port
  if ! command -v "${cmd%% *}" >/dev/null; then
    echo "TXE server '$cmd' not found: install @aztec-labs/txe@6.0.0, set TXE, or set SKIP_TXE=1" >&2
    exit 1
  fi
  port=$(python3 -I -c 'import socket; s = socket.socket(); s.bind(("127.0.0.1", 0)); print(s.getsockname()[1])')
  TXE_PORT=$port LOG_LEVEL=${LOG_LEVEL:-warn} $cmd &
  txe_pid=$!
  for _ in $(seq 150); do
    (exec 3<>"/dev/tcp/127.0.0.1/$port") 2>/dev/null && break
    kill -0 "$txe_pid" 2>/dev/null || { echo "TXE server exited" >&2; exit 1; }
    sleep 0.2
  done
  (exec 3<>"/dev/tcp/127.0.0.1/$port") 2>/dev/null || { echo "TXE server did not start" >&2; exit 1; }
  txe_url=http://127.0.0.1:$port
}
