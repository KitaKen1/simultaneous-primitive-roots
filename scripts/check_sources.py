#!/usr/bin/env python3
"""Check the publication contract without invoking any submitted Lean code."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def lean_code(text):
    """Remove nested comments and string literals while preserving line numbers."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            if c == '\\' and i + 1 < len(text):
                out.extend('  ')
                i += 2
            else:
                string = c != '"'
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        elif c == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(c)
            i += 1
    if depth or string:
        raise ValueError('Unclosed Lean comment or string')
    return ''.join(out)


def check_port_record(current_hashes):
    """Reconstruct pre-port sources, using only the published patch and files."""
    original = json.loads((ROOT / 'ci/original-source-sha256.json').read_text())['files']
    record = json.loads((ROOT / 'ci/port-changes.json').read_text())
    changed = record['changed_existing_files']
    changed_by_file = {entry['file']: entry for entry in changed}
    assert len(changed_by_file) == len(changed), 'Duplicate port-record file'
    assert set(original) <= set(current_hashes), 'Original proof files were removed'
    expected_changed = {rel for rel, before in original.items() if current_hashes[rel] != before}
    assert set(changed_by_file) == expected_changed, 'Stale or incomplete port-change record'
    for rel, entry in changed_by_file.items():
        assert entry['before_sha256'] == original[rel], rel
        assert entry['after_sha256'] == current_hashes[rel], rel
    publication_proofs = {'Challenge.lean', 'Solution.lean',
                          'SimultaneousPrimitiveRootsFinal/OpenAIMain.lean'}
    new = set(current_hashes) - set(original) - publication_proofs
    assert set(record['new_proof_backports']) == new, 'Unrecorded new proof source'

    lines = (ROOT / 'ci/lean4331-port.patch').read_text().splitlines(keepends=True)
    hunk = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@')
    i, patched = 0, set()
    while i < len(lines):
        assert lines[i].startswith('--- original/'), 'Invalid original patch header'
        rel = lines[i][len('--- original/'):].rstrip('\n')
        assert rel in changed_by_file and rel not in patched, rel
        i += 1
        assert lines[i] == f'+++ lean4331/{rel}\n', rel
        i += 1
        current = (ROOT / 'lean' / rel).read_bytes().decode('utf-8').splitlines(keepends=True)
        cursor, reconstructed = 0, []
        while i < len(lines) and not lines[i].startswith('--- original/'):
            match = hunk.match(lines[i])
            assert match, f'{rel}: invalid patch hunk'
            old_count = int(match[2] or 1)
            new_count = int(match[4] or 1)
            new_start = int(match[3]) - (1 if new_count else 0)
            assert cursor <= new_start <= len(current), rel
            reconstructed.extend(current[cursor:new_start])
            cursor, seen_old, seen_new = new_start, 0, 0
            i += 1
            while i < len(lines) and not lines[i].startswith(('@@ ', '--- original/')):
                line = lines[i]
                assert line[0] in ' +-', f'{rel}: invalid patch line'
                if line[0] in ' +':
                    assert cursor < len(current) and current[cursor] == line[1:], \
                        f'{rel}: patch does not match current source'
                    cursor += 1
                    seen_new += 1
                if line[0] in ' -':
                    reconstructed.append(line[1:])
                    seen_old += 1
                i += 1
            assert (seen_old, seen_new) == (old_count, new_count), rel
        reconstructed.extend(current[cursor:])
        assert hashlib.sha256(''.join(reconstructed).encode()).hexdigest() == original[rel], \
            f'{rel}: patch does not reconstruct the recorded original source'
        patched.add(rel)
    assert patched == expected_changed, 'Patch omits changed files'
    return {'passed': True, 'changed_existing_files': len(changed), 'new_proof_backports': len(new),
            'added_publication_proofs': ['SimultaneousPrimitiveRootsFinal/OpenAIMain.lean']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-port-record', action='store_true',
                        help='also validate the completed migration digests and unified patch')
    args = parser.parse_args()
    lock = json.loads((ROOT / 'ci/toolchain-lock.json').read_text())
    assert lock['lean_toolchain'] == 'leanprover/lean4:v4.33.1', 'Publication requires Lean v4.33.1'
    for rel, expected in json.loads((ROOT / 'ci/checking-tool-sha256.json').read_text()).items():
        assert hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == expected, rel
    for rel in ['lean', 'tools/comparator', 'tools/lean4export', 'tools/fc-style', 'ci/comparator-controls']:
        assert (ROOT / rel / 'lean-toolchain').read_text().strip() == lock['lean_toolchain'], rel
    challenge = ROOT / 'lean/Challenge.lean'
    assert re.findall(r'^import\s+(\S+)', challenge.read_text(), re.M) == ['Mathlib'], 'Challenge must be independent of the proof and FC utilities'
    fc_statement = ROOT / 'FClikelean/SimultaneousPrimitiveRoots.lean'
    fc_auxiliary = ROOT / 'FClikelean/SquareConditionNecessary.lean'
    # All three central statements and the supplement are independent targets.
    def declaration(path, name):
        code = lean_code(path.read_text())
        return re.sub(r'\s+', '', re.search(
            rf'\btheorem {name}\b.*?\bby\s+sorry\b', code, re.S).group())
    for name, path in [('simultaneous_primitive_roots', fc_statement),
                       ('simultaneous_primitive_roots_unconditional', fc_statement),
                       ('positive_lower_density', fc_statement),
                       ('square_condition_necessary', fc_auxiliary)]:
        assert declaration(challenge, name) == declaration(path, name), \
            f'{name} differs from the independently reviewed statement'
    config = json.loads((ROOT / 'lean/comparator.json').read_text())
    assert config == {
        'challenge_module': 'Challenge',
        'solution_module': 'SimultaneousPrimitiveRootsFinal.OpenAIMain',
        'theorem_names': [
            'SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots',
            'SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional',
            'SimultaneousPrimitiveRootsChallenge.positive_lower_density',
            'SimultaneousPrimitiveRootsChallenge.square_condition_necessary'],
        'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
        'enable_nanoda': False}, 'Unexpected public comparator configuration'
    fc_manifest = json.loads((ROOT / 'tools/fc-style/lake-manifest.json').read_text())
    fc_packages = {p['name']: p for p in fc_manifest['packages']}
    assert fc_packages['formal_conjectures']['rev'] == '79eac378a26b46d30974cdb33962e0752591b79d'
    assert fc_packages['mathlib']['rev'] == lock['mathlib']['commit']
    manifest = json.loads((ROOT / 'lean/lake-manifest.json').read_text())
    mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
    assert mathlib['rev'] == lock['mathlib']['commit']
    for package in manifest['packages']:
        assert re.fullmatch(r'[0-9a-f]{40}', package['rev']), package['name']
    digest = hashlib.sha256()
    files = 0
    current_hashes = {}
    forbidden = re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|debug\.skipKernelTC')
    for path in sorted((ROOT / 'lean').rglob('*.lean')):
        if '.lake' in path.parts:
            continue
        source = path.read_bytes()
        code = lean_code(source.decode('utf-8'))
        if path == challenge:
            assert len(re.findall(r'\bsorry\b', code)) == 4
            code = re.sub(r'\bsorry\b', '', code)
        match = forbidden.search(code)
        assert not match, f'{path.relative_to(ROOT)}:{code[:match.start()].count(chr(10)) + 1}: {match[0]}'
        digest.update(str(path.relative_to(ROOT)).encode() + b'\0' + source)
        current_hashes[str(path.relative_to(ROOT / 'lean'))] = hashlib.sha256(source).hexdigest()
        files += 1
    result = {'passed': True, 'lean_files': files, 'source_sha256': digest.hexdigest(),
              'intentional_statement_placeholders': 4}
    fc_digest, fc_files = hashlib.sha256(), 0
    fc_sources = sorted((ROOT / 'FClikelean').rglob('*.lean'))
    expected_theorems = {
        fc_statement: ['simultaneous_primitive_roots', 'simultaneous_primitive_roots_unconditional',
                       'positive_lower_density'],
        fc_auxiliary: ['square_condition_necessary'],
    }
    assert fc_sources == sorted(expected_theorems), 'Unexpected FC statement files'
    for path in fc_sources:
        source = path.read_bytes()
        code = lean_code(source.decode('utf-8'))
        assert re.findall(r'\btheorem\s+(\w+)', code) == expected_theorems[path]
        assert len(re.findall(r'\bsorry\b', code)) == len(expected_theorems[path])
        code = re.sub(r'\bsorry\b', '', code)
        match = forbidden.search(code)
        assert not match, f'{path.relative_to(ROOT)}: {match[0]}'
        imports = re.findall(r'^(?:public )?import\s+(\S+)', code, re.M)
        assert imports == ['FormalConjecturesUtil'], f'Unexpected FC standard import: {imports}'
        assert len(re.findall(r'@\[category research solved, AMS 11,', code)) == len(expected_theorems[path])
        assert len(re.findall(r'formal_proof using lean4 at', code)) == len(expected_theorems[path])
        fc_digest.update(str(path.relative_to(ROOT)).encode() + b'\0' + source)
        fc_files += 1
    main_proof = ROOT / 'lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean'
    def theorem_type(path, name):
        code = lean_code(path.read_text())
        return re.sub(r'\s+', '', re.search(rf'\btheorem {name}\b.*?(?=:= by)', code, re.S).group())
    assert theorem_type(main_proof, 'simultaneous_primitive_roots') == theorem_type(fc_statement, 'simultaneous_primitive_roots')
    for name in ['HeckeZeroFreeHypothesis', 'roughDensity', 'MarkedTypeIIHypothesis',
                 'BlockSieveHypothesis', 'RoughDensityHypothesis']:
        pattern = rf'(?:noncomputable )?def {name}\b.*?(?=\n/--)'
        assert re.sub(r'\s+', '', re.search(pattern, main_proof.read_text(), re.S).group()) == re.sub(r'\s+', '', re.search(pattern, fc_statement.read_text(), re.S).group()), name
        assert re.sub(r'\s+', '', re.search(pattern, challenge.read_text(), re.S).group()) == re.sub(r'\s+', '', re.search(pattern, fc_statement.read_text(), re.S).group()), name
    for name in ['HeckeZeroFreeHypothesis', 'MarkedTypeIIHypothesis',
                 'BlockSieveHypothesis', 'RoughDensityHypothesis']:
        code = lean_code(fc_statement.read_text())
        assert f'def {name} : Prop :=' in code, f'Undefined hypothesis {name}'
    result['fclikelean'] = {'lean_files': fc_files, 'source_sha256': fc_digest.hexdigest(),
                            'intentional_statement_placeholders': 4,
                            'input_definition_placeholders': 0,
                            'main_self_contained': True, 'auxiliary_separate': True,
                            'standard_import': 'FormalConjecturesUtil',
                            'all_theorems_category': 'research solved', 'AMS': [11]}
    if args.check_port_record:
        result['port_record'] = check_port_record(current_hashes)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
