#!/usr/bin/env python3
"""Transfer only same-commit Linux component build objects; never transfer a Challenge.

The first configured component whose import closure contains a module owns all of
that module's build outputs. Archives contain a manifest first, then regular build
files. Merge validates every archive into private staging before changing .lake/build.
This is an operational cache; the unchanged final Comparator still validates proofs.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
GIB = 1024 ** 3
MAX_MANIFEST_BYTES = 32 * 1024 ** 2
MAX_PAYLOAD_BYTES = 32 * GIB
MAX_FILE_BYTES = 4 * GIB
NAME = re.compile(r"[a-z][a-z0-9-]*")
HASH = re.compile(r"[0-9a-f]{64}")
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
IMPORT = re.compile(r"^(?:(?:public|meta|private)\s+)*import\s+([^\n]+)", re.M)
TOKEN = re.compile(r"(?:«[^»]*»|[^\s«»])+")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def sha_file(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 ** 2), b''):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f'Duplicate JSON key: {key}')
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


def lean_code(text):
    """Remove nested comments and strings while retaining import line boundaries."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        c, pair = text[i], text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            if c == '\\' and i + 1 < len(text):
                i += 2
            else:
                string = c != '"'
                out.append('\n' if c == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif c == '"':
            string = True
            i += 1
        else:
            out.append(c)
            i += 1
    require(not depth and not string, 'Unclosed Lean comment or string')
    return ''.join(out)


def module_name(parts):
    return '.'.join(p if IDENT.fullmatch(p) else f'«{p}»' for p in parts)


def import_name(token):
    parts, current, quoted = [], [], False
    for c in token:
        if c == '«':
            require(not quoted and not current, f'Invalid import: {token}')
            quoted = True
        elif c == '»':
            require(quoted, f'Invalid import: {token}')
            quoted = False
        elif c == '.' and not quoted:
            require(current, f'Empty import segment: {token}')
            parts.append(''.join(current))
            current = []
        else:
            current.append(c)
    require(current and not quoted, f'Invalid import: {token}')
    parts.append(''.join(current))
    return module_name(parts)


class Plan:
    def __init__(self, root):
        self.root = Path(root).resolve()
        self.lean = self.root / 'lean'
        self.config = read_json((self.root / 'ci/component-targets.json').read_bytes())
        require(self.config.get('schema_version') == 1, 'Unsupported component schema')
        self.components = self.config['components']
        names = [c['name'] for c in self.components]
        require(names and len(names) == len(set(names)), 'Duplicate or empty components')
        require(all(isinstance(n, str) and NAME.fullmatch(n) for n in names), 'Invalid component name')
        self.names = names
        known = set()
        for c in self.components:
            require(set(c) == {'name', 'targets', 'dependencies'}, 'Unexpected component fields')
            require(c['targets'] and len(c['targets']) == len(set(c['targets'])), 'Empty/duplicate roots')
            require(set(c['dependencies']) <= known, 'Dependencies must precede their component')
            known.add(c['name'])
        lake = tomllib.loads((self.lean / 'lakefile.toml').read_text())
        source_roots = {self.lean.resolve()}
        source_roots.update((self.lean / lib.get('srcDir', '.')).resolve()
                            for lib in lake.get('lean_lib', []))
        source_roots = sorted(source_roots, key=lambda p: len(p.parts), reverse=True)
        self.sources, self.output_bases, self.raw, self.sizes = {}, {}, {}, {}
        paths = []
        for directory, dirs, files in os.walk(self.lean, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d not in ('.lake', '.git'))
            for filename in sorted(files):
                if filename.endswith('.lean'):
                    paths.append(Path(directory) / filename)
        source_digest = hashlib.sha256()
        for path in sorted(paths):
            require(not path.is_symlink(), f'Symlink source: {path}')
            source_root = next(p for p in source_roots if path.is_relative_to(p))
            parts = path.relative_to(source_root).with_suffix('').parts
            name = module_name(parts)
            require(name not in self.sources, f'Duplicate source module: {name}')
            raw = path.read_bytes()
            self.sources[name], self.raw[name], self.sizes[name] = path, raw, len(raw)
            self.output_bases[name] = '/'.join(parts)
            source_digest.update(path.relative_to(self.root).as_posix().encode() + b'\0' + raw)
        self.source_sha256 = source_digest.hexdigest()
        self.modules_by_base = {v: k for k, v in self.output_bases.items()}
        self.graph = {}
        for name, raw in self.raw.items():
            imports = [import_name(t) for m in IMPORT.finditer(lean_code(raw.decode()))
                       for t in TOKEN.findall(m.group(1))]
            self.graph[name] = set(imports) & self.sources.keys()
        self.full = self.closure([self.config['final_module']])
        self.closures, self.owners = {}, {}
        for component in self.components:
            name = component['name']
            closure = self.closure(component['targets'])
            require(closure <= self.full, f'Component contains modules outside final proof: {name}')
            require(not any(n == 'Challenge' or n.startswith('Challenge.') for n in closure),
                    'Challenge cannot be shared')
            self.closures[name] = closure
            for module in sorted(closure):
                self.owners.setdefault(module, name)
        self.assembly = set(self.config['final_assembly_modules'])
        require(self.full - self.owners.keys() == self.assembly,
                'Component coverage differs from the explicit final assembly modules')
        require(not self.assembly & self.owners.keys(), 'Final assembly cannot be prebuilt')
        self.owners_sha256 = hashlib.sha256(canonical(self.owners)).hexdigest()

    def closure(self, roots):
        require(all(r in self.sources for r in roots), f'Unknown local root: {roots}')
        seen, pending = set(), list(roots)
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(self.graph[name] - seen)
        return seen

    def owned(self, component):
        require(component in self.names, f'Unknown component: {component}')
        return sorted(n for n, owner in self.owners.items() if owner == component)

    def report(self):
        return {'schema_version': 1, 'component_names': self.names,
                'components': [{**c, 'closure_modules': len(self.closures[c['name']]),
                                'closure_source_bytes': sum(self.sizes[n] for n in self.closures[c['name']]),
                                'owned_modules': len(self.owned(c['name']))}
                               for c in self.components],
                'full_module_count': len(self.full), 'covered_module_count': len(self.owners),
                'final_assembly_modules': sorted(self.assembly),
                'module_owners_sha256': self.owners_sha256,
                'source_sha256': self.source_sha256}

    def artifact_module(self, path):
        parts = path.split('/')
        require(path and not path.startswith('/') and '\\' not in path and '\x00' not in path
                and all(p not in ('', '.', '..') for p in parts), f'Unsafe archive path: {path}')
        require(not path.endswith(('.lean', '.py', '.sh', '.bash', '.toml', '.md', '.yml', '.yaml')),
                f'Source/document files cannot be shared: {path}')
        if parts[:2] == ['lib', 'lean']:
            offset, families = 2, {'olean', 'ilean', 'ir', 'trace', 'o', 'so', 'a'}
        elif parts[:1] == ['ir']:
            offset, families = 1, {'c', 'setup', 'o', 'bc', 'll'}
        else:
            raise ValueError(f'Not a permitted proof build path: {path}')
        require(len(parts) > offset, f'Invalid build path: {path}')
        filename = parts[-1]
        for i in reversed([i for i, c in enumerate(filename) if c == '.']):
            base = '/'.join(parts[offset:-1] + [filename[:i]])
            suffix = filename[i + 1:]
            if base in self.modules_by_base and suffix.split('.')[0] in families:
                module = self.modules_by_base[base]
                require(module in self.owners and module != 'Challenge',
                        f'Module is not a shareable component output: {module}')
                return module
        raise ValueError(f'Unrecognized build object: {path}')


def commit_identity(root, explicit=None):
    result = subprocess.run(['git', '-C', str(root), 'rev-parse', '--verify', 'HEAD'],
                            text=True, capture_output=True)
    head = result.stdout.strip() if result.returncode == 0 else None
    claimed = explicit or os.environ.get('GITHUB_SHA') or head
    require(isinstance(claimed, str) and re.fullmatch(r'[0-9a-f]{40}', claimed), 'Need a full Git commit')
    require(head is None or claimed == head, 'Requested commit differs from Git HEAD')
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        require(head is not None and os.environ.get('GITHUB_SHA') == head,
                'CI requires matching Git HEAD and GITHUB_SHA')
    if head is not None:
        require(subprocess.run(['git', '-C', str(root), 'diff', '--quiet', 'HEAD', '--']).returncode == 0,
                'Tracked files differ from the claimed commit')
        untracked = subprocess.check_output(
            ['git', '-C', str(root), 'ls-files', '--others', '--exclude-standard'], text=True)
        require(not untracked.strip(), 'Untracked files are outside the claimed commit')
    return claimed


def identity(plan, commit=None):
    require(platform.system() == 'Linux' and platform.machine() == 'x86_64',
            'Only Linux x86_64 build objects may be shared')
    paths = ['lean/lean-toolchain', 'lean/lakefile.toml', 'lean/lake-manifest.json',
             'ci/component-targets.json', 'ci/build-component.lean',
             'ci/toolchain-lock.json', 'ci/checking-tool-sha256.json', 'scripts/ci-build-artifacts.py']
    for tool in ('comparator', 'lean4export'):
        paths.extend(f'tools/{tool}/{p}' for p in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'))
    hashes = {p: sha_file(plan.root / p) for p in paths}
    compiler = subprocess.check_output(['lean', '--version'], cwd=plan.lean, text=True).strip()
    toolchain = (plan.lean / 'lean-toolchain').read_text().strip()
    require(toolchain == 'leanprover/lean4:v4.33.1' and 'version 4.33.1,' in compiler,
            'Component artifacts require the pinned Lean 4.33.1 compiler')
    return {'commit': commit_identity(plan.root, commit), 'platform': 'Linux-x86_64',
            'workflow_run': {key: os.environ.get(key) for key in
                             ('GITHUB_REPOSITORY', 'GITHUB_RUN_ID')},
            'toolchain': toolchain, 'compiler': compiler, 'source_sha256': plan.source_sha256,
            'input_sha256': hashes, 'module_owners_sha256': plan.owners_sha256,
            'options': {'lakefile_sha256': hashes['lean/lakefile.toml'],
                        'safe_lake_LEAN_ABORT_ON_PANIC': '1', 'bounded_lake_LEAN_NUM_THREADS': '2'}}


def check_module_outputs(plan, directory, modules, paths):
    """Require primary outputs and every companion output named by Lake's trace."""
    for module in modules:
        base = plan.output_bases[module]
        trace = f'lib/lean/{base}.trace'
        required = {trace, f'lib/lean/{base}.olean', f'lib/lean/{base}.olean.hash'}
        require(required <= paths, f'Missing primary outputs for {module}')
        document = read_json((directory / trace).read_bytes())
        outputs = document.get('outputs')
        require(isinstance(outputs, dict) and isinstance(outputs.get('o'), list),
                f'Invalid Lake trace output list: {module}')
        for key, values in outputs.items():
            if key == 'm':
                continue
            require(key in ('o', 'i', 'c', 'r', 'rs'), f'Unknown Lake output kind: {key}')
            values = values if isinstance(values, list) else [values]
            for value in values:
                require(isinstance(value, str) and '.' in value, f'Invalid trace output: {module}')
                suffix = value.split('.', 1)[1]
                prefix = 'ir' if key == 'c' else 'lib/lean'
                path = f'{prefix}/{base}.{suffix}'
                require(plan.artifact_module(path) == module, f'Unexpected trace output: {path}')
                required.update((path, path + '.hash'))
                if key == 'c':
                    required.add(f'ir/{base}.setup.json')
        require(required <= paths, f'Missing companion outputs for {module}: {sorted(required - paths)}')


def regular_file(path):
    mode = path.lstat().st_mode
    require(stat.S_ISREG(mode) and not path.is_symlink(), f'Not a regular build file: {path}')


def pack(plan, component, output, commit=None):
    expected_identity = identity(plan, commit)
    owned = plan.owned(component)
    build = plan.lean / '.lake/build'
    no_symlink_parents(build)
    require(build.is_dir() and not build.is_symlink(), 'Missing or symlinked build directory')
    records = []
    for subtree in ('lib/lean', 'ir'):
        directory = build / subtree
        no_symlink_parents(directory)
        require(not directory.is_symlink(), f'Symlink build subtree: {directory}')
        if not directory.exists():
            continue
        for parent, dirs, files in os.walk(directory, followlinks=False):
            for d in dirs:
                require(not (Path(parent) / d).is_symlink(), 'Symlink in build directory')
            for filename in sorted(files):
                path = Path(parent) / filename
                regular_file(path)
                relative = path.relative_to(build).as_posix()
                try:
                    module = plan.artifact_module(relative)
                except ValueError:
                    # Unowned/unused/final/Challenge outputs are deliberately never exported.
                    continue
                if plan.owners[module] != component:
                    continue
                info = path.stat()
                require(info.st_size <= MAX_FILE_BYTES, f'Oversized build file: {relative}')
                records.append({'path': relative, 'module': module, 'bytes': info.st_size,
                                'sha256': sha_file(path), 'mode': stat.S_IMODE(info.st_mode) & 0o777,
                                'mtime_ns': info.st_mtime_ns})
    records.sort(key=lambda entry: entry['path'])
    paths = {entry['path'] for entry in records}
    check_module_outputs(plan, build, owned, paths)
    total = sum(entry['bytes'] for entry in records)
    require(total <= MAX_PAYLOAD_BYTES, 'Component build payload exceeds the size limit')
    manifest = {'schema_version': 1, 'component': component, 'identity': expected_identity,
                'owned_modules': owned, 'files': records}
    encoded = canonical(manifest)
    require(len(encoded) <= MAX_MANIFEST_BYTES, 'Manifest exceeds the size limit')
    output = Path(output).absolute()
    require(not output.exists() and not output.is_symlink(), f'Archive already exists: {output}')
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + f'.partial-{os.getpid()}')
    try:
        with temporary.open('xb') as raw:
            with gzip.GzipFile(fileobj=raw, mode='wb', compresslevel=1, mtime=0) as compressed:
                with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as archive:
                    header = tarfile.TarInfo('manifest.json')
                    header.size, header.mode = len(encoded), 0o644
                    import io
                    archive.addfile(header, io.BytesIO(encoded))
                    for entry in records:
                        path = build / entry['path']
                        regular_file(path)
                        info = path.stat()
                        require(info.st_size == entry['bytes'] and info.st_mtime_ns == entry['mtime_ns'],
                                f'Build object changed while packing: {path}')
                        header = tarfile.TarInfo(entry['path'])
                        header.size, header.mode = entry['bytes'], entry['mode']
                        header.mtime = entry['mtime_ns'] // 10 ** 9
                        with path.open('rb') as stream:
                            archive.addfile(header, stream)
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    return {'component': component, 'archive': str(output), 'owned_modules': len(owned),
            'files': len(records), 'payload_bytes': total, 'archive_sha256': sha_file(output)}


def validate_manifest(plan, manifest, expected_identity, selected):
    require(set(manifest) == {'schema_version', 'component', 'identity', 'owned_modules', 'files'},
            'Unexpected archive manifest fields')
    require(manifest['schema_version'] == 1 and manifest['identity'] == expected_identity,
            'Artifact identity differs from the current commit/compiler/sources/options')
    component = manifest['component']
    require(component in selected, f'Unexpected component archive: {component}')
    require(manifest['owned_modules'] == plan.owned(component), 'Incorrect module owner coverage')
    files = manifest['files']
    require(isinstance(files, list) and len(files) <= 200000, 'Invalid file list')
    entries = {}
    for entry in files:
        require(set(entry) == {'path', 'module', 'bytes', 'sha256', 'mode', 'mtime_ns'}, 'Invalid file record')
        path = entry['path']
        module = plan.artifact_module(path)
        require(path not in entries, f'Duplicate manifest path: {path}')
        require(module == entry['module'] and plan.owners[module] == component, f'Wrong owner: {path}')
        require(type(entry['bytes']) is int and 0 <= entry['bytes'] <= MAX_FILE_BYTES, 'Invalid file size')
        require(isinstance(entry['sha256'], str) and HASH.fullmatch(entry['sha256']), 'Invalid SHA256')
        require(type(entry['mode']) is int and 0 <= entry['mode'] <= 0o777, 'Unsafe file mode')
        require(type(entry['mtime_ns']) is int and entry['mtime_ns'] >= 0, 'Invalid file timestamp')
        entries[path] = entry
    require(sum(e['bytes'] for e in files) <= MAX_PAYLOAD_BYTES, 'Oversized component archive')
    return component, entries


def no_symlink_parents(path):
    for part in (path, *path.parents):
        require(not part.is_symlink(), f'Symlink destination: {part}')


def merge(plan, archives, components=None, commit=None):
    expected_identity = identity(plan, commit)
    selected = set(components if components is not None else plan.names)
    require(selected and selected <= set(plan.names), 'Unknown/empty selected components')
    require(len(archives) == len(selected), 'Need exactly one archive per selected component')
    build = plan.lean / '.lake/build'
    no_symlink_parents(build)
    build.parent.mkdir(parents=True, exist_ok=True)
    seen_components, all_entries = set(), {}
    # Stage before committing any output, so malformed later archives cannot partially merge.
    with tempfile.TemporaryDirectory(prefix='.component-merge-', dir=build.parent) as temporary:
        staging = Path(temporary)
        for filename in archives:
            filename = Path(filename)
            regular_file(filename)
            with tarfile.open(filename, mode='r|gz') as archive:
                first = archive.next()
                require(first is not None and first.name == 'manifest.json' and first.type == tarfile.REGTYPE
                        and first.size <= MAX_MANIFEST_BYTES, 'Archive must start with a regular manifest')
                source = archive.extractfile(first)
                require(source is not None, 'Missing archive manifest')
                manifest = read_json(source.read())
                component, entries = validate_manifest(plan, manifest, expected_identity, selected)
                require(component not in seen_components, f'Duplicate component archive: {component}')
                require(not all_entries.keys() & entries.keys(), 'Overlapping archive output paths')
                remaining = sum(e['bytes'] for e in entries.values())
                require(shutil.disk_usage(staging).free >= remaining + 4 * GIB,
                        'Insufficient disk for validated merge and runner diagnostics')
                extracted = set()
                # Do not use extractall: every path, file kind, owner and hash is checked explicitly.
                for member in archive:
                    # Stream iteration can yield the first header again after archive.next().
                    if member is first:
                        continue
                    require(member.name in entries and member.name not in extracted,
                            f'Unexpected or duplicate tar member: {member.name}')
                    entry = entries[member.name]
                    require(member.type in (tarfile.REGTYPE, tarfile.AREGTYPE) and not member.sparse
                            and not any(k.startswith('GNU.sparse') for k in member.pax_headers),
                            f'Non-regular tar member: {member.name}')
                    require(member.size == entry['bytes'] and member.mode == entry['mode'],
                            f'Tar metadata mismatch: {member.name}')
                    path = staging / PurePosixPath(member.name)
                    path.parent.mkdir(parents=True, exist_ok=True)
                    digest = hashlib.sha256()
                    incoming = archive.extractfile(member)
                    require(incoming is not None, f'Missing payload: {member.name}')
                    with path.open('xb') as outgoing:
                        for chunk in iter(lambda: incoming.read(1024 ** 2), b''):
                            digest.update(chunk)
                            outgoing.write(chunk)
                    require(digest.hexdigest() == entry['sha256'], f'Payload hash mismatch: {member.name}')
                    os.chmod(path, entry['mode'])
                    os.utime(path, ns=(entry['mtime_ns'], entry['mtime_ns']))
                    extracted.add(member.name)
                require(extracted == entries.keys(), 'Missing artifact payload files')
                check_module_outputs(plan, staging, plan.owned(component), extracted)
                seen_components.add(component)
                all_entries.update(entries)
        require(seen_components == selected, 'Missing component archives')
        expected_modules = {m for m, owner in plan.owners.items() if owner in selected}
        require({e['module'] for e in all_entries.values()} == expected_modules, 'Incomplete module coverage')
        for relative in all_entries:
            target = build / PurePosixPath(relative)
            no_symlink_parents(target)
            require(not target.exists(), f'Refusing to overwrite an existing build object: {target}')
        for relative in sorted(all_entries):
            target = build / PurePosixPath(relative)
            target.parent.mkdir(parents=True, exist_ok=True)
            os.replace(staging / PurePosixPath(relative), target)
    return {'components': [c for c in plan.names if c in selected], 'modules': len(expected_modules),
            'files': len(all_entries), 'payload_bytes': sum(e['bytes'] for e in all_entries.values()),
            'identity': expected_identity}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--commit', help='Explicit full commit for isolated fixtures; must match HEAD if present')
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('plan')
    commands.add_parser('identity')
    packing = commands.add_parser('pack')
    packing.add_argument('--component', required=True)
    packing.add_argument('--output', type=Path, required=True)
    merging = commands.add_parser('merge')
    merging.add_argument('--archive', type=Path, action='append', required=True)
    merging.add_argument('--component', action='append', help='Explicit subset; default requires every component')
    args = parser.parse_args()
    plan = Plan(args.root)
    if args.command == 'plan':
        result = plan.report()
    elif args.command == 'identity':
        result = identity(plan, args.commit)
    elif args.command == 'pack':
        result = pack(plan, args.component, args.output, args.commit)
    else:
        result = merge(plan, args.archive, args.component, args.commit)
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, tarfile.TarError, subprocess.SubprocessError) as error:
        print(f'Component artifact error: {error}', file=sys.stderr)
        raise SystemExit(1)
