#!/usr/bin/env python3
"""Keep CI diagnostics outside the comparator's sandbox and systemd unit."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
GIB = 1024 ** 3


def snapshot():
    disk = shutil.disk_usage(ROOT)
    memory = {}
    proc = Path('/proc/meminfo')
    if proc.exists():
        for line in proc.read_text().splitlines():
            key, value = line.split(':', 1)
            if key in ('MemTotal', 'MemAvailable', 'SwapTotal', 'SwapFree'):
                memory[key + '_kib'] = int(value.split()[0])
    return {
        'utc': datetime.now(timezone.utc).isoformat(),
        'disk_free_gib': round(disk.free / GIB, 2),
        'disk_total_gib': round(disk.total / GIB, 2),
        **memory,
    }, disk.free


def monitor(unit, log, flag, min_free_gib):
    if sys.platform != 'linux' or not re.fullmatch(r'spr-[A-Za-z0-9-]+\.service', unit):
        raise ValueError('Expected a Linux spr-* systemd service owned by this invocation')
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('a', buffering=1) as stream:
        while True:
            data, available = snapshot()
            line = 'CI resources: ' + json.dumps(data, sort_keys=True)
            print(line, flush=True)
            print(line, file=stream, flush=True)
            if available < min_free_gib * GIB:
                message = f'Low disk: stopping {unit} before runner logs are lost.'
                flag.write_text(message + '\n')
                print(message, flush=True)
                print(message, file=stream, flush=True)
                subprocess.run(['sudo', 'systemctl', 'stop', unit], check=True, timeout=60)
                return 3
            time.sleep(30)


def control():
    """Exercise an actual cgroup stop without filling the runner's disk."""
    if sys.platform != 'linux':
        raise ValueError('The resource-guard control requires Linux')
    unit = f'spr-disk-guard-control-{os.getpid()}.service'
    log = ROOT / 'ci/results/resource-guard-control.log'
    flag = ROOT / 'ci/results/resource-guard-control-triggered.txt'
    log.parent.mkdir(parents=True, exist_ok=True)
    flag.unlink(missing_ok=True)
    try:
        subprocess.run([
            'sudo', 'systemd-run', '--quiet', '--collect', f'--unit={unit}',
            f'--uid={os.getuid()}', f'--gid={os.getgid()}', '/usr/bin/sleep', '120',
        ], check=True)
        result = monitor(unit, log, flag, 1_000_000)
        active = subprocess.run(['systemctl', 'is-active', '--quiet', unit]).returncode == 0
        if result != 3 or not flag.exists() or active:
            raise RuntimeError('The disk guard did not stop its test unit')
    finally:
        subprocess.run(['sudo', 'systemctl', 'stop', unit], stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, check=False)
    print('Resource guard control passed: low-disk abort stopped the test unit.', flush=True)
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('preflight', 'monitor', 'control'))
    parser.add_argument('--min-free-gib', type=float, default=4)
    parser.add_argument('--unit')
    parser.add_argument('--log', type=Path)
    parser.add_argument('--flag', type=Path)
    args = parser.parse_args()
    if args.mode == 'control':
        return control()
    if args.mode == 'preflight':
        data, available = snapshot()
        print(json.dumps(data, sort_keys=True), flush=True)
        if available < args.min_free_gib * GIB:
            print(f'Insufficient disk: need {args.min_free_gib:g} GiB free before the proof.',
                  file=sys.stderr)
            return 2
        return 0
    if not all((args.unit, args.log, args.flag)):
        parser.error('monitor requires --unit, --log and --flag')
    return monitor(args.unit, args.log, args.flag, args.min_free_gib)


if __name__ == '__main__':
    raise SystemExit(main())
