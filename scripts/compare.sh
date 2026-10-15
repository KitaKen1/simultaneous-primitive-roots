#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
mode=${1:-linux}
python3 "$root/scripts/check_sources.py"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
mkdir -p "$root/ci/results"
cd "$root/tools/comparator"
lake build comparator lean4export
export COMPARATOR_LEAN4EXPORT="$root/tools/lean4export/.lake/build/bin/lean4export"
binary="$root/tools/comparator/.lake/build/bin/comparator"
cd "$root/lean"
# Upstream Comparator forwards PATH into Landrun but not LEAN_NUM_THREADS.
# Keep this native launcher outside the candidate's writable .lake tree.
bounded_bin=$(bash "$root/scripts/prepare-comparator-runtime.sh")
export PATH="$bounded_bin:$PATH"
case "$mode" in
  local-development)
    export COMPARATOR_LANDRUN="$root/tools/comparator/scripts/fake-landrun.sh"
    echo 'Local development: official macOS shim; Linux sandbox has not been exercised.'
    lake env "$binary" comparator.json 2>&1 | tee "$root/ci/results/comparator-local.log"
    ;;
  linux)
    [[ $(uname -s) == Linux ]] || { echo 'Use local-development for macOS.' >&2; exit 2; }
    : "${COMPARATOR_LANDRUN:?Set COMPARATOR_LANDRUN to the pinned Linux landrun binary}"
    [[ $COMPARATOR_LANDRUN != *fake-landrun* ]] || { echo 'Linux CI requires real Landrun.' >&2; exit 2; }
    python3 "$root/scripts/monitor-linux-resources.py" preflight --min-free-gib 4
    unit="spr-comparator-$$.service"
    guard_flag="$root/ci/results/disk-guard-triggered.txt"
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
    # Restrict AF_UNIX independently of Landrun (upstream comparator guidance).
    # The transient unit runs as the current unprivileged user.
    (
      sudo systemd-run --quiet --wait --pipe --collect \
        --unit="$unit" \
        --uid="$(id -u)" --gid="$(id -g)" \
        --property=RestrictAddressFamilies=~AF_UNIX \
        --property=TimeoutStopSec=15s --property=KillMode=control-group \
        --working-directory="$PWD" \
        --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
        --setenv="LEAN_NUM_THREADS=$LEAN_NUM_THREADS" \
        --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
        --setenv="COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
        "$bounded_bin/lake" env "$binary" comparator.json 2>&1 | tee "$root/ci/results/comparator-linux.log"
    ) &
    comparison_pid=$!
    # Do not ask the guard to stop a unit that has not been created yet.
    while kill -0 "$comparison_pid" 2>/dev/null; do
      if systemctl is-active --quiet "$unit"; then
        python3 "$root/scripts/monitor-linux-resources.py" monitor \
          --unit "$unit" --log "$root/ci/results/resources.log" --flag "$guard_flag" &
        monitor_pid=$!
        break
      fi
      sleep 0.2
    done
    while kill -0 "$comparison_pid" 2>/dev/null; do
      if [[ -z $monitor_pid ]] || ! kill -0 "$monitor_pid" 2>/dev/null; then
        echo 'Resource monitor stopped unexpectedly; aborting comparison.' > "$guard_flag"
        sudo systemctl stop "$unit" || true
        break
      fi
      sleep 2
    done
    comparison_status=0
    wait "$comparison_pid" || comparison_status=$?
    if [[ -z $monitor_pid ]] || ! kill -0 "$monitor_pid" 2>/dev/null; then
      echo 'Comparison cannot pass without its resource monitor.' >&2
      comparison_status=1
    fi
    if [[ -e $guard_flag ]]; then
      cat "$guard_flag" >&2
      comparison_status=1
    fi
    exit "$comparison_status"
    ;;
  *) echo 'Usage: scripts/compare.sh [linux|local-development]' >&2; exit 2 ;;
esac
