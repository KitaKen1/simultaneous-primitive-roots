#!/usr/bin/env python3
"""Compile each independent FC statement without the publication's built libraries."""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / 'tools/fc-style'
STATEMENTS = [ROOT / 'FClikelean' / name for name in
              ['SimultaneousPrimitiveRoots.lean', 'OpenAIConditional.lean',
               'SquareConditionNecessary.lean']]


def main():
    lake = shutil.which('lake')
    assert lake, 'lake is required'
    for statement in STATEMENTS:
        imports = re.findall(r'^(?:public )?import\s+(\S+)', statement.read_text(), re.M)
        assert imports == ['FormalConjecturesUtil'], imports
    assert sorted((ROOT / 'FClikelean').rglob('*.lean')) == sorted(STATEMENTS)

    def lake_env(*args):
        return subprocess.check_output([lake, 'env', *args], cwd=LEAN_DIR, text=True).strip()

    paths = [Path(p) if Path(p).is_absolute() else LEAN_DIR / p
             for p in lake_env('printenv', 'LEAN_PATH').split(os.pathsep) if p]
    own_build = (LEAN_DIR / '.lake/build/lib/lean').resolve()
    remaining = [str(p.resolve()) for p in paths if p.resolve() != own_build]
    assert len(remaining) < len(paths), 'Publication build path was not found'
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(remaining)
    lean = lake_env('which', 'lean')
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version, version
    results = []
    with tempfile.TemporaryDirectory(prefix='fc-statement-') as directory:
        for statement in STATEMENTS:
            result = subprocess.run([lean, '-j1', str(statement)], cwd=directory, env=env,
                                    capture_output=True, text=True)
            results.append({'file': str(statement.relative_to(ROOT)),
                            'exit_code': result.returncode,
                            'compiler_output': result.stdout + result.stderr})
    passed = all(result['exit_code'] == 0 for result in results)
    print(json.dumps({
        'passed': passed,
        'lean_version': version,
        'each_file_self_contained': True,
        'standard_import': 'FormalConjecturesUtil',
        'real_fc_attributes': True,
        'own_statement_build_path_removed': True,
        'files': results,
    }, indent=2))
    raise SystemExit(0 if passed else 1)


if __name__ == '__main__':
    main()
