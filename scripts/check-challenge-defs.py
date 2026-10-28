#!/usr/bin/env python3
"""Require exact shared definition blocks and Mathlib-only Challenge imports."""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MARK = re.compile(r'^-- (BEGIN|END) SHARED DEFINITIONS(?:: ([A-Za-z0-9_]+))?')

def blocks(path):
    result = {}
    active = None
    saved = []
    for line in path.read_bytes().decode('utf-8').splitlines(keepends=True):
        match = MARK.match(line)
        if match:
            kind, name = match.groups()
            name = name or 'Defs'
            if kind == 'BEGIN':
                if active is not None or name in result:
                    raise ValueError(f'{path.name}: nested or duplicate block {name}')
                active, saved = name, []
            elif active != name:
                raise ValueError(f'{path.name}: unmatched end {name}')
        if active is not None:
            saved.append(line)
        if match and match[1] == 'END':
            result[active] = ''.join(saved)
            active = None
    if active is not None:
        raise ValueError(f'{path.name}: unfinished block {active}')
    return result

def main():
    challenge = ROOT / 'CD2015Challenge.lean'
    actual = blocks(challenge)
    required = {'Defs', 'GrowthDefs', 'StochDefs'}
    if set(actual) != required:
        raise ValueError('Challenge must contain exactly Defs, GrowthDefs, StochDefs')
    for name in sorted(required):
        expected = blocks(ROOT / 'ChenDalang15' / (name + '.lean'))
        if set(expected) != {name} or actual[name] != expected[name]:
            raise ValueError(f'{name}: shared definition block differs')
    imports = re.findall(
        r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)',
        challenge.read_text(), re.M)
    bad = [m for m in imports if not (m == 'Mathlib' or m.startswith('Mathlib.'))]
    if not imports or bad:
        raise ValueError(f'non-Mathlib imports: {bad}')
    print(f'challenge-defs: PASS ({len(imports)} Mathlib imports; 3 exact shared blocks)')

if __name__ == '__main__':
    try:
        main()
    except (ValueError, UnicodeError) as exc:
        sys.exit(f'challenge-defs: FAIL ({exc})')
