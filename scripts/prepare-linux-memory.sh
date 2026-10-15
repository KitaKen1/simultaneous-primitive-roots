#!/usr/bin/env bash
set -euo pipefail
[[ ${GITHUB_ACTIONS:-} == true && ${RUNNER_OS:-} == Linux ]] || {
  echo 'This script configures only an ephemeral GitHub-hosted Linux runner.' >&2
  exit 2
}
free -h
df -h .
# These preinstalled SDKs are unused by this Lean-only ephemeral job.
sudo rm -rf /usr/local/lib/android /usr/share/dotnet /opt/ghc /opt/hostedtoolcache/CodeQL
df -h .
[[ ${1:-} != --no-swap ]] || exit 0
swap_file="${RUNNER_TEMP:?}/simultaneous-primitive-roots.swap"
available_kib=$(df -Pk "$RUNNER_TEMP" | awk 'END {print $4}')
swap_mib=$((available_kib / 1024 - 16 * 1024))
(( swap_mib <= 16 * 1024 )) || swap_mib=$((16 * 1024))
(( swap_mib >= 8 * 1024 )) || {
  echo 'Insufficient free disk for swap while reserving 16 GiB for Lean builds.' >&2
  exit 2
}
sudo fallocate -l "${swap_mib}M" "$swap_file"
sudo chmod 600 "$swap_file"
sudo mkswap "$swap_file"
sudo swapon "$swap_file"
free -h
df -h .
