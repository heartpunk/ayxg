"""Bounded fresh-WRUH-extraction versus shared native observer comparison."""
import argparse
import json
import os
import random
import subprocess
import tempfile
from pathlib import Path

from ayxg import (ArraySort, BoolSort, BVSort, Declaration, QFAbvArrayValue,
                  QFAbvContext, QFAbvExpr, QFAbvValuation, eval_expr)
from ayxg.codec import loads

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / 'tests/regressions/sudo-pcmpgtb'
TARGET = 0x400170


def extract_model(work, occurrence, wruh_root, wruh_fresh):
    encoded = (FIXTURES / f'{occurrence}.bin').read_bytes()
    # The observer also places these exact bytes at 0x400170. RET is only
    # extraction scaffolding after the target, never part of the observation.
    source = '.text\n.globl wruh_pbt_target\n.type wruh_pbt_target,@function\nwruh_pbt_target:\n'
    source += '.byte ' + ','.join(f'0x{byte:02x}' for byte in encoded) + '\n.byte 0xc3\n'
    source += '.size wruh_pbt_target, .-wruh_pbt_target\n.section .note.GNU-stack,"",@progbits\n'
    (work / 'stub.S').write_text(source)
    subprocess.run(['as', '--64', '-o', str(work / 'stub.o'), str(work / 'stub.S')], check=True)
    subprocess.run(['ld', '--build-id=none', '-Ttext=0x400170', '-e', 'wruh_pbt_target',
                    '-o', str(work / 'stub.elf'), str(work / 'stub.o')], check=True)
    env = dict(os.environ, WRUH_AYXG_SOURCE=str(ROOT), PYTHONDONTWRITEBYTECODE='1')
    subprocess.run([str(wruh_fresh), '--artifact', str(work / 'stub.elf'), '--root',
                    'wruh_pbt_target', '--root-only', '--output', str(work / 'model.json')],
                   cwd=wruh_root, env=env, check=True, timeout=180)
    payload = loads((work / 'model.json').read_text())
    function, = (f for f in payload['functions'] if f['function_id'] == 'wruh_pbt_target')
    matching = [o for o in function['occurrences'] if o['origin']['canonical_address'] == TARGET
                and o['origin']['instruction_bytes'] == encoded.hex()]
    occurrence_record, = matching
    edge, = (e for e in function['local_edges'] if e['source'] == TARGET and
             e['edge_id']['static_occurrence_id'] == occurrence_record['static_occurrence_id'])
    return function, edge


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--observer', type=Path, required=True)
    parser.add_argument('--observer-fixtures', type=Path, required=True)
    parser.add_argument('--wruh-root', type=Path, required=True)
    parser.add_argument('--wruh-fresh', type=Path, required=True)
    parser.add_argument('--examples', type=int, default=12)
    parser.add_argument('--seed', type=int, default=270933)
    args = parser.parse_args()
    if args.examples < 1:
        parser.error('--examples must be positive')
    rng = random.Random(args.seed)
    boundary = [0, 1, 0x7e, 0x7f, 0x80, 0x81, 0xfe, 0xff]
    cases = [(933, 'zmm0', 'zmm6', 0, 6), (934, 'zmm1', 'zmm0', 1, 0)]
    for occurrence, dest, src, dest_index, src_index in cases:
        with tempfile.TemporaryDirectory(prefix='ayxg-pcmpgtb-extract-') as extraction:
            function, edge = extract_model(Path(extraction), occurrence, args.wruh_root.resolve(), args.wruh_fresh.resolve())
            declarations = tuple(Declaration.from_data(d) for d in function['declarations'])
            ctx = QFAbvContext(declarations)
            update = next(v['value'] for v in edge['summary']['simultaneous_update'] if v['name'] == dest)
            expr = QFAbvExpr(ctx, BVSort(512), update)
            guard = QFAbvExpr(ctx, BoolSort(), edge['summary']['guard'])
            for index in range(args.examples):
                left = bytes(rng.choice(boundary) if i < 8 else rng.randrange(256) for i in range(16))
                right = bytes(rng.choice(boundary) if i < 8 else rng.randrange(256) for i in range(16))
                values = []
                for declaration in declarations:
                    sort = declaration.sort
                    if sort.kind == 'array':
                        values.append(QFAbvArrayValue(ArraySort(sort.index_width, sort.value_width), 0))
                    elif sort.kind == 'bool':
                        values.append(False)
                    elif sort.kind == 'bv':
                        values.append(int.from_bytes(left if declaration.name == dest else right, 'little')
                                      if declaration.name in (dest, src) else TARGET if declaration.name == 'rip' else 0)
                    else:
                        raise ValueError(f'unsupported declaration sort: {sort.kind}')
                state = QFAbvValuation(ctx, tuple(values))
                if not eval_expr(guard, state):
                    raise AssertionError('extracted target guard is false')
                model = eval_expr(expr, state).to_bytes(64, 'little')[:16]
                with tempfile.TemporaryDirectory(prefix='ayxg-pcmpgtb-native-') as tmp:
                    work = Path(tmp)
                    (work / 'input').write_bytes(left + right)
                    cmd = ['bwrap', '--unshare-all', '--unshare-user', '--disable-userns',
                           '--cap-drop', 'ALL', '--clearenv', '--new-session', '--die-with-parent',
                           '--ro-bind', '/nix/store', '/nix/store', '--ro-bind', '/run/current-system/sw', '/run/current-system/sw',
                           '--ro-bind', str(args.observer.resolve()), '/observer',
                           '--ro-bind', str(args.observer_fixtures.resolve()), '/fixtures',
                           '--ro-bind', str((FIXTURES / f'{occurrence}.bin').resolve()), '/instruction',
                           '--bind', str(work), '/work', '--proc', '/proc', '--dev', '/dev',
                           '--setenv', 'PATH', '/run/current-system/sw/bin',
                           '--', '/observer', '/fixtures', '/work', '/instruction', '/work/input',
                           '/work/output', str(dest_index), str(src_index)]
                    subprocess.run(cmd, check=True, timeout=15)
                    actual = (work / 'output').read_bytes()
                if actual != model:
                    raise AssertionError(f'occurrence={occurrence} case={index} seed={args.seed} '
                                         f'left={left.hex()} right={right.hex()} model={model.hex()} native={actual.hex()}')
        print(f'PASS occurrence={occurrence} cases={args.examples} seed={args.seed}', flush=True)


if __name__ == '__main__':
    main()
