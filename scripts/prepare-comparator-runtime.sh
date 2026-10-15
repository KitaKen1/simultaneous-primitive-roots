#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root/lean"
real_lake="$(lean --print-prefix)/bin/lake"
bounded_bin="$root/tools/runtime/.lake/bin"
mkdir -p "$bounded_bin"
# Quote the compiler definition as a C string, including unusual path characters.
real_lake_c=${real_lake//\\/\\\\}
real_lake_c=${real_lake_c//\"/\\\"}
# Landrun's --add-exec/--ldd handles native ELF files, not shell interpreters.
cc -O2 -Wall -Wextra -Werror "-DREAL_LAKE=\"$real_lake_c\"" \
  "$root/scripts/bounded-lake.c" -o "$bounded_bin/lake"
printf '%s\n' "$bounded_bin"
