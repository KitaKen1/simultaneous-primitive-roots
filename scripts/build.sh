#!/usr/bin/env bash
set -euo pipefail
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
python3 "$root/scripts/check_sources.py"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
export MATHLIB_CACHE_DIR="$root/lean/.lake/mathlib-cache"
mkdir -p "$root/ci/results"
cd "$root/lean"
lake exe cache get 2>&1 | tee "$root/ci/results/cache.log"
lake build Challenge Solution 2>&1 | tee "$root/ci/results/build.log"
lake env lean Solution.lean | tee "$root/ci/results/axioms.log"
python3 - "$root/ci/results/axioms.log" "$root/lean/comparator.json" <<'PY'
import json, re, sys
from pathlib import Path
reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", Path(sys.argv[1]).read_text())
expected = {'SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional',
            'SimultaneousPrimitiveRootsChallenge.positive_lower_density',
            'SimultaneousPrimitiveRootsChallenge.square_condition_necessary'}
assert len(reports) == len(expected) and {name for name, _ in reports} == expected, reports
config = json.loads(Path(sys.argv[2]).read_text())
submitted = ['SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional',
             'SimultaneousPrimitiveRootsChallenge.positive_lower_density']
assert config['challenge_module'] == 'Challenge' and config['solution_module'] == 'Solution', config
assert config['theorem_names'] == submitted, config['theorem_names']
assert set(submitted) <= {name for name, _ in reports}, reports
permitted = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == permitted and config['enable_nanoda'] is False, config
for name, axioms in reports:
    assert {a.strip() for a in axioms.split(',')} == permitted, name
print('Both submitted proofs and the square-condition supplement use only the three permitted axioms.')
print('Comparator targets: ' + ', '.join(config['theorem_names']))
PY
