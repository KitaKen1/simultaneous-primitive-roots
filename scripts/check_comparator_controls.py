#!/usr/bin/env python3
"""Verify that the pinned comparator accepts/rejects three tiny controls."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    env = dict(os.environ)
    bounded_bin = subprocess.check_output(
        ['bash', str(ROOT / 'scripts/prepare-comparator-runtime.sh')], text=True).strip()
    env['PATH'] = bounded_bin + os.pathsep + env['PATH']
    env['COMPARATOR_LEAN4EXPORT'] = str(ROOT / 'tools/lean4export/.lake/build/bin/lean4export')
    local = os.uname().sysname != 'Linux'
    if local:
        env['COMPARATOR_LANDRUN'] = str(ROOT / 'tools/comparator/scripts/fake-landrun.sh')
    else:
        assert env.get('COMPARATOR_LANDRUN'), 'Linux controls require the pinned Landrun binary'
    binary = ROOT / 'tools/comparator/.lake/build/bin/comparator'
    results = ROOT / 'ci/results'
    results.mkdir(exist_ok=True)
    records = []
    for name, accepted, marker in [
        ('ControlSolution', True, 'Your solution is okay!'),
        ('ControlWrongType', False, 'theorem statement'),
        ('ControlExtraAxiom', False, 'forbidden')]:
        command = ['lake', 'env', str(binary), name + '.json']
        run = subprocess.run(command, cwd=ROOT / 'ci/comparator-controls', env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        log = results / (name + '.log')
        log.write_text(run.stdout)
        assert (run.returncode == 0) == accepted, (name, run.returncode, run.stdout)
        assert marker in run.stdout, (name, run.stdout)
        records.append({'case': name, 'exit_code': run.returncode,
                        'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()})
        print('PASS', name, flush=True)
    (results / 'comparator-controls.json').write_text(json.dumps({
        'passed': True, 'macos_development_shim': local, 'controls': records,
        'complete_public_solution_checked': False}, indent=2) + '\n')


if __name__ == '__main__':
    main()
