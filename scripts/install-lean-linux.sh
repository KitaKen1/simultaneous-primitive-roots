#!/usr/bin/env bash
set -euo pipefail
[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] || {
  echo 'This installer targets the Ubuntu x86_64 CI runner.' >&2; exit 2;
}
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
install_dir=$(mktemp -d)
trap 'rm -rf "$install_dir"' EXIT
curl --fail --location --retry 3 \
  https://github.com/leanprover/elan/releases/download/v4.2.3/elan-x86_64-unknown-linux-gnu.tar.gz \
  -o "$install_dir/elan.tar.gz"
tar -xzf "$install_dir/elan.tar.gz" -C "$install_dir"
"$install_dir/elan-init" -y --default-toolchain none
if [[ -n ${GITHUB_PATH:-} ]]; then
  printf '%s\n' "$HOME/.elan/bin" >> "$GITHUB_PATH"
fi
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat "$root/lean/lean-toolchain")"
cd "$root/lean"
lean --version
