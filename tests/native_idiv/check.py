"""Compare fresh WRUH IDIV models to the shared native observer on safe inputs.

This is a small instruction-specific integration check, not a general PBT runner.
"""
import argparse
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

from ayxg import (ArraySort, Declaration, QFAbvArrayValue, QFAbvContext,
                  QFAbvExpr, QFAbvValuation, eval_expr)
from ayxg import codec
from ayxg.qfabv import decode_sort

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/chroot_print_int_idiv.json"
MASK = (1 << 64) - 1
ADDRESS = 0x100000000
PC = 0x400170


def run(command, **kwargs):
    subprocess.run([str(x) for x in command], check=True, timeout=180, **kwargs)


def evaluate(node, context, state):
    return eval_expr(QFAbvExpr(context, decode_sort(node.sort), node), state)


def extract(wruh, executable, instruction, directory):
    asm = directory / 'stub.S'
    asm.write_text('.text\n.globl wruh_pbt_target\n.type wruh_pbt_target,@function\n'
                   'wruh_pbt_target:\n.byte ' + ','.join(hex(b) for b in instruction) +
                   '\n.byte 0xc3\n.size wruh_pbt_target,.-wruh_pbt_target\n'
                   '.section .note.GNU-stack,"",@progbits\n')
    obj, binary, output = (directory / name for name in ('stub.o', 'stub', 'model.json'))
    run(['as', '--64', '-o', obj, asm])
    run(['ld', '--build-id=none', '-Ttext=0x400170', '-e', 'wruh_pbt_target', '-o', binary, obj])
    env = dict(os.environ, WRUH_AYXG_SOURCE=str(ROOT))
    run([executable, '--artifact', binary, '--root', 'wruh_pbt_target', '--root-only',
         '--output', output], cwd=wruh, env=env)
    artifact = codec.loads(output.read_text())
    functions = artifact['functions']
    matches = [(function, occurrence) for function in functions for occurrence in function['occurrences']
               if occurrence['origin']['canonical_address'] == PC
               and occurrence['origin']['instruction_bytes'] == instruction.hex()]
    if len(matches) != 1:
        raise ValueError('fresh extraction did not identify the exact stub instruction')
    function, occurrence = matches[0]
    edges = [edge for edge in function['local_edges'] if edge['source'] == PC and
             edge['edge_id']['static_occurrence_id'] == occurrence['static_occurrence_id']]
    if not edges:
        raise ValueError('fresh extraction has no edges for the stub instruction')
    return QFAbvContext(tuple(Declaration.from_data(d) for d in function['declarations'])), edges


def observe(observer, fixtures, instruction_file, work, rax, rdx, divisor):
    (work / 'input').write_bytes(b''.join(x.to_bytes(8, 'little') for x in (rax, rdx, divisor)))
    run(['bwrap', '--unshare-all', '--unshare-user', '--disable-userns', '--cap-drop', 'ALL',
         '--clearenv', '--new-session', '--die-with-parent', '--ro-bind', '/nix/store', '/nix/store',
         '--ro-bind', '/run/current-system/sw', '/run/current-system/sw', '--ro-bind', observer, '/observer',
         '--ro-bind', fixtures, '/fixtures', '--ro-bind', instruction_file, '/instruction',
         '--bind', work, '/work', '--proc', '/proc', '--dev', '/dev',
         '--setenv', 'PATH', '/nix/var/nix/profiles/default/bin:/run/current-system/sw/bin',
         '--', '/observer', '/fixtures', '/work', '/instruction', '/work/input', '/work/output'])
    result = (work / 'output').read_bytes()
    if len(result) != 16:
        raise ValueError('observer did not return both GPRs')
    return tuple(int.from_bytes(result[i:i + 8], 'little') for i in (0, 8))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wruh-source', required=True, type=Path)
    parser.add_argument('--wruh-fresh', required=True, type=Path)
    parser.add_argument('--observer', required=True, type=Path)
    parser.add_argument('--observer-fixtures', required=True, type=Path)
    parser.add_argument('--examples', type=int, default=12)
    parser.add_argument('--seed', type=int, default=260013)
    args = parser.parse_args()
    if not 1 <= args.examples <= 100:
        parser.error('--examples must be between 1 and 100')
    wruh, executable, observer, fixtures = (p.resolve(strict=True) for p in
        (args.wruh_source, args.wruh_fresh, args.observer, args.observer_fixtures))
    rng = random.Random(args.seed)
    fixture = json.loads(FIXTURE.read_text())
    cases = fixture['cases']
    with tempfile.TemporaryDirectory(prefix='ayxg-idiv-') as tmp:
        root = Path(tmp)
        for case in cases:
            origin = case['occurrence']['origin']
            if (origin['image_sha256'] != fixture['binary_sha256'] or
                fixture['function_id'] not in origin['function_owners'] or
                origin['architecture'] != 'AMD64'):
                raise ValueError('instruction fixture provenance is inconsistent')
            instruction = bytes.fromhex(origin['instruction_bytes'])
            directory = root / str(case['occurrence']['static_occurrence_id'])
            directory.mkdir()
            instruction_file = directory / 'instruction'
            instruction_file.write_bytes(instruction)
            context, edges = extract(wruh, executable, instruction, directory)
            for index in range(args.examples):
                # Sign-extended 64-bit dividends guarantee a representable quotient,
                # except MIN / -1, which is explicitly rejected.
                while True:
                    dividend = rng.randrange(-(1 << 63), 1 << 63)
                    divisor = rng.randrange(-(1 << 63), 1 << 63)
                    if divisor and (dividend, divisor) != (-(1 << 63), -1):
                        break
                rax, rdx, divbits = dividend & MASK, (MASK if dividend < 0 else 0), divisor & MASK
                mem = QFAbvArrayValue(ArraySort(64, 8), 0, tuple(
                    (ADDRESS + i, byte) for i, byte in enumerate(divbits.to_bytes(8, 'little')) if byte))
                values = {'rax': rax, 'rdx': rdx, 'rdi': divbits, 'rbp': ADDRESS + 0x58,
                          'rip': PC, 'mem': mem, 'd': 1}
                def value(declaration):
                    if declaration.name in values:
                        return values[declaration.name]
                    if declaration.sort.kind == 'bv':
                        return 0
                    if declaration.sort.kind == 'bool':
                        return False
                    if declaration.sort.kind == 'array':
                        return QFAbvArrayValue(decode_sort(declaration.sort), 0)
                    raise ValueError(f'unsupported state sort for {declaration.name}')
                state = QFAbvValuation(context, tuple(value(d) for d in context.declarations))
                selected = [e for e in edges if evaluate(e['summary']['guard'], context, state)]
                if len(selected) != 1:
                    raise AssertionError(f'expected one enabled edge, got {len(selected)}')
                updates = {item['name']: item['value'] for item in selected[0]['summary']['simultaneous_update']}
                model = tuple(evaluate(updates[name], context, state) for name in ('rax', 'rdx'))
                actual = observe(observer, fixtures, instruction_file, directory, rax, rdx, divbits)
                if model != actual:
                    raise AssertionError(f'{instruction.hex()} seed={args.seed} case={index} '
                                         f'dividend={dividend} divisor={divisor} model={model} native={actual}')
                if index == 0:
                    print(f'example bytes={instruction.hex()} dividend={dividend} divisor={divisor} '
                          f'model_rax={model[0]:016x} model_rdx={model[1]:016x} '
                          f'native_rax={actual[0]:016x} native_rdx={actual[1]:016x}', flush=True)
            print(f"PASS bytes={instruction.hex()} original_address={origin['canonical_address']:#x} "
                  f"occurrence={case['occurrence']['static_occurrence_id']} "
                  f'examples={args.examples} seed={args.seed}', flush=True)


if __name__ == '__main__':
    main()
