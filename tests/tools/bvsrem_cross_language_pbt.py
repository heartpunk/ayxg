"""Compare AYXG's Python and Lean bvsrem evaluators with Z3 on shared cases."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

import z3

from ayxg import BVSort, Declaration, QFAbvContext, QFAbvExpr, QFAbvValuation, eval_expr
from ayxg.expr import TermSort
from ayxg.z3 import expr_from_z3


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "tests/fixtures/bvsrem.json"
LEAN_CHECK = ROOT / "tests/lean/BvSRemGeneratedCases.lean"
SEED = 0xB5E2026


@dataclass(frozen=True)
class BvSRemCase:
    """The shared JSON record consumed by the Python and Lean checkers."""

    width: int
    left: int
    right: int
    expected: int


def generated_inputs(seed: int) -> list[tuple[int, int, int]]:
    cases: list[tuple[int, int, int]] = []

    # Exhaust small widths so every signed-remainder combination, including
    # divisor zero, is covered at the widths where exhaustive enumeration is cheap.
    for width in (1, 2, 3, 4):
        cases.extend(
            (width, left, right)
            for left in range(1 << width)
            for right in range(1 << width)
        )

    rng = random.Random(seed)
    for width in (8, 16, 32, 64, 128):
        sign = 1 << (width - 1)
        mask = (1 << width) - 1
        boundaries = (0, 1, sign - 1, sign, sign + 1, mask - 1, mask)
        cases.extend((width, left, right) for left in boundaries for right in boundaries)
        cases.extend(
            (width, rng.getrandbits(width), rng.getrandbits(width))
            for _ in range(12)
        )

    return cases


def oracle_result(width: int, left: int, right: int, ctx: z3.Context) -> int:
    lhs = z3.BitVecVal(left, width, ctx=ctx)
    rhs = z3.BitVecVal(right, width, ctx=ctx)
    return z3.simplify(z3.SRem(lhs, rhs)).as_long()


def check_python(cases: list[BvSRemCase]) -> None:
    z3_ctx = z3.Context()
    expressions: dict[int, tuple[QFAbvContext, QFAbvExpr]] = {}

    for case in cases:
        width = case.width
        if width not in expressions:
            lhs, rhs = z3.BitVecs("lhs rhs", width, ctx=z3_ctx)
            typed = expr_from_z3(z3.SRem(lhs, rhs))
            context = QFAbvContext((
                Declaration("lhs", TermSort.bv(width)),
                Declaration("rhs", TermSort.bv(width)),
            ))
            expressions[width] = (context, QFAbvExpr(context, BVSort(width), typed))

        context, expression = expressions[width]
        actual = eval_expr(expression, QFAbvValuation(context, (case.left, case.right)))
        if actual != case.expected:
            raise AssertionError(
                f"Python bvsrem mismatch: {case}; expected={case.expected}, actual={actual}"
            )


def main() -> None:
    fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
    if fixture.get("operator") != "bv_srem":
        raise AssertionError("shared fixture operator must be bv_srem")

    z3_ctx = z3.Context()
    raw_cases: list[tuple[int, int, int, int | None]] = []
    for item in fixture["cases"]:
        raw_cases.append((item["width"], item["left"], item["right"], item["expected"]))
    raw_cases.extend((*item, None) for item in generated_inputs(SEED))

    # Keep the common record set deterministic while avoiding repeated fixture
    # vectors that also occur in exhaustive or boundary generation.
    unique: dict[tuple[int, int, int], BvSRemCase] = {}
    for width, left, right, fixture_expected in raw_cases:
        expected = oracle_result(width, left, right, z3_ctx)
        if fixture_expected is not None and fixture_expected != expected:
            raise AssertionError(
                f"shared fixture disagrees with Z3: {(width, left, right)} "
                f"fixture={fixture_expected}, Z3={expected}"
            )
        unique[(width, left, right)] = BvSRemCase(width, left, right, expected)
    cases = list(unique.values())

    check_python(cases)

    payload = {
        "operator": "bv_srem",
        "seed": SEED,
        "cases": [asdict(case) for case in cases],
    }
    with tempfile.TemporaryDirectory(prefix="ayxg-bvsrem-pbt-") as temporary:
        cases_path = Path(temporary) / "cases.json"
        cases_path.write_text(json.dumps(payload), encoding="utf-8")
        env = dict(os.environ, AYXG_BVSREM_PBT_CASES=str(cases_path))
        subprocess.run(
            ["lake", "env", "lean", str(LEAN_CHECK)],
            cwd=ROOT,
            env=env,
            check=True,
            timeout=120,
        )

    print(f"PASS bvsrem cross-language cases={len(cases)} seed={SEED}")


if __name__ == "__main__":
    main()
