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
    # Restrict AF_UNIX independently of Landrun (upstream comparator guidance).
    # The transient unit runs as the current unprivileged user.
    sudo systemd-run --quiet --wait --pipe --collect \
      --uid="$(id -u)" --gid="$(id -g)" \
      --property=RestrictAddressFamilies=~AF_UNIX \
      --working-directory="$PWD" \
      --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
      --setenv="LEAN_NUM_THREADS=$LEAN_NUM_THREADS" \
      --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_LEAN4EXPORT" \
      --setenv="COMPARATOR_LANDRUN=$COMPARATOR_LANDRUN" \
      "$bounded_bin/lake" env "$binary" comparator.json 2>&1 | tee "$root/ci/results/comparator-linux.log"
    ;;
  *) echo 'Usage: scripts/compare.sh [linux|local-development]' >&2; exit 2 ;;
esac
