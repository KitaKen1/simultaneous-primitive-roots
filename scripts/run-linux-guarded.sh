#!/usr/bin/env bash
# Operational resource guard shared by component compilation and full comparison.
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
label=${1:?Expected a log label and an absolute command}
shift
[[ $label =~ ^[a-z0-9-]+$ ]] || { echo 'Invalid log label.' >&2; exit 2; }
[[ $(uname -s) == Linux ]] || { echo 'This wrapper requires Linux.' >&2; exit 2; }
[[ $# -gt 0 && $1 == /* && -x $1 ]] || { echo 'Expected an absolute executable path.' >&2; exit 2; }
mkdir -p "$root/ci/results"
python3 "$root/scripts/monitor-linux-resources.py" preflight --min-free-gib 4
unit="spr-$label-$$.service"
guard_flag="$root/ci/results/$label-guard-triggered.txt"
resource_log="$root/ci/results/resources-$label.log"
rm -f -- "$guard_flag"
monitor_pid=''
cleanup() {
  sudo systemctl stop "$unit" >/dev/null 2>&1 || true
  if [[ -n $monitor_pid ]]; then
    kill "$monitor_pid" 2>/dev/null || true
    wait "$monitor_pid" 2>/dev/null || true
  fi
}
trap cleanup EXIT
trap 'exit 143' TERM
trap 'exit 130' INT
(
  sudo systemd-run --quiet --wait --pipe --collect \
    --unit="$unit" \
    --uid="$(id -u)" --gid="$(id -g)" \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --property=TimeoutStopSec=15s --property=KillMode=control-group \
    --working-directory="$PWD" \
    --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
    --setenv="LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}" \
    --setenv="LEAN_PATH=${LEAN_PATH:-}" \
    --setenv="COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-}" \
    --setenv="COMPARATOR_LANDRUN=${COMPARATOR_LANDRUN:-}" \
    "$@" 2>&1 | tee "$root/ci/results/$label-linux.log"
) &
command_pid=$!
started=$SECONDS
while kill -0 "$command_pid" 2>/dev/null; do
  if systemctl is-active --quiet "$unit"; then
    python3 "$root/scripts/monitor-linux-resources.py" monitor \
      --unit "$unit" --log "$resource_log" --flag "$guard_flag" &
    monitor_pid=$!
    break
  fi
  if (( SECONDS - started > 30 )); then
    echo 'Verification unit did not become active.' > "$guard_flag"
    sudo systemctl stop "$unit" || true
    break
  fi
  sleep 0.2
done
while kill -0 "$command_pid" 2>/dev/null; do
  if [[ -z $monitor_pid ]] || ! kill -0 "$monitor_pid" 2>/dev/null; then
    echo 'Resource monitor stopped unexpectedly; aborting verification.' > "$guard_flag"
    sudo systemctl stop "$unit" || true
    break
  fi
  sleep 2
done
command_status=0
wait "$command_pid" || command_status=$?
if [[ -z $monitor_pid ]] || ! kill -0 "$monitor_pid" 2>/dev/null; then
  echo 'Verification cannot pass without its resource monitor.' >&2
  command_status=1
fi
if [[ -e $guard_flag ]]; then
  cat "$guard_flag" >&2
  command_status=1
fi
exit "$command_status"
