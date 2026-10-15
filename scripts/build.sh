#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
python3 "$root/scripts/check_sources.py"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export MATHLIB_CACHE_DIR="$root/lean/.lake/mathlib-cache"
mkdir -p "$root/ci/results"
cd "$root/lean"
lake exe cache get 2>&1 | tee "$root/ci/results/cache.log"
lake build Challenge Solution SimultaneousPrimitiveRootsFinal.OpenAIMain 2>&1 | tee "$root/ci/results/build.log"
lake env lean Solution.lean | tee "$root/ci/results/axioms.log"
lake env lean SimultaneousPrimitiveRootsFinal/OpenAIMain.lean | tee -a "$root/ci/results/axioms.log"
python3 - "$root/ci/results/axioms.log" <<'PY'
import re, sys
from pathlib import Path
reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", Path(sys.argv[1]).read_text())
expected = {'SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots',
            'SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional',
            'SimultaneousPrimitiveRootsChallenge.positive_lower_density',
            'SimultaneousPrimitiveRootsChallenge.square_condition_necessary'}
assert {name for name, _ in reports} == expected, reports
for name, axioms in reports:
    assert {a.strip() for a in axioms.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}, name
print('All four public proofs depend only on the three permitted axioms.')
PY
