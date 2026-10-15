#!/usr/bin/env bash
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo 'Landrun requires Linux.' >&2; exit 2; }
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
rev=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["landrun"]["commit"])' "$root/ci/toolchain-lock.json")
dest="$root/tools/landrun/.lake/source"
mkdir -p "$dest"
git -C "$dest" init --quiet
git -C "$dest" remote get-url origin >/dev/null 2>&1 || \
  git -C "$dest" remote add origin https://github.com/Zouuup/landrun.git
git -C "$dest" fetch --depth=1 origin "$rev"
git -C "$dest" checkout --detach FETCH_HEAD
[[ $(git -C "$dest" rev-parse HEAD) == "$rev" ]]
cd "$dest"
go build -trimpath -o ../landrun ./cmd/landrun
printf 'COMPARATOR_LANDRUN=%s\n' "$root/tools/landrun/.lake/landrun" >> "${GITHUB_ENV:?This installer is for GitHub Actions}"
