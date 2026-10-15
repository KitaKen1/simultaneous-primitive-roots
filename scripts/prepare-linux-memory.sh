#!/usr/bin/env bash
set -euo pipefail
[[ ${GITHUB_ACTIONS:-} == true && ${RUNNER_OS:-} == Linux &&
   ${RUNNER_ENVIRONMENT:-} == github-hosted ]] || {
  echo 'This script configures only an ephemeral GitHub-hosted Linux runner.' >&2
  exit 2
}
free -h
df -h .
# These SDKs are unused by this plain Lean job on a disposable hosted runner.
# Preserve system Python, C/C++, Git and the Actions runner's own Node runtime.
sudo rm -rf /usr/local/lib/android /usr/share/dotnet /opt/ghc \
  /usr/share/swift /usr/local/.ghcup /usr/lib/jvm /usr/share/miniconda \
  /usr/local/share/powershell /usr/local/share/chromium "$HOME/.rustup"
# setup-go installs the pinned Go version later. Keep its writable cache root.
if [[ -d /opt/hostedtoolcache ]]; then
  sudo find /opt/hostedtoolcache -mindepth 1 -maxdepth 1 -exec rm -rf -- {} +
fi
if command -v docker >/dev/null 2>&1; then
  timeout 120s sudo docker image prune --all --force || true
fi
df -h .
[[ ${1:-} != --no-swap ]] || exit 0
swap_file="${RUNNER_TEMP:?}/simultaneous-primitive-roots.swap"
available_kib=$(df -Pk "$RUNNER_TEMP" | awk 'END {print $4}')
swap_mib=$((available_kib / 1024 - 36 * 1024))
(( swap_mib <= 16 * 1024 )) || swap_mib=$((16 * 1024))
(( swap_mib >= 8 * 1024 )) || {
  echo 'Insufficient free disk for swap while reserving 36 GiB for Lean builds.' >&2
  exit 2
}
sudo fallocate -l "${swap_mib}M" "$swap_file"
sudo chmod 600 "$swap_file"
sudo mkswap "$swap_file"
sudo swapon "$swap_file"
free -h
df -h .
