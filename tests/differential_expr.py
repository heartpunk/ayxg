"""Hypothesis differential checks against actual Lean AYXG expression evaluation.

Usage: python tests/differential_expr.py --bridge-project /tmp/ayxg-bridge
The bridge is built once, then called in-process through the actual lean.py FFI.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
import subprocess
import sys
import select
from pathlib import Path
from typing import Any

from hypothesis import given, settings, strategies as st
from hypothesis.database import DirectoryBasedExampleDatabase
from lean_py import LeanLibrary

from ayxg import Declaration, QFAbvArrayValue, QFAbvContext, QFAbvExpr, QFAbvValuation, TermSort, TypedExpr, eval_expr
from ayxg.qfabv import ArraySort, Value, decode_sort

BV_OPS = ("bv_add", "bv_sub", "bv_mul", "bv_udiv", "bv_sdiv", "bv_urem", "bv_and", "bv_or", "bv_xor", "bv_shl", "bv_lshr", "bv_ashr")
CMP_OPS = ("bv_ult", "bv_ule", "bv_slt", "bv_sle")
OPS = ("var", "bool_lit", "bv_lit", "const_array", "bool_not", "bool_and", "bool_or", "ite", "eq", *BV_OPS, "bv_not", "zero_extend", "sign_extend", "extract", "concat", "select", "store", *CMP_OPS)


def numbers(width: int):
    mask = (1 << width) - 1
    return st.one_of(st.sampled_from([0, 1, mask, mask >> 1, 1 << (width - 1)]), st.integers(0, mask))


@dataclass
class Case:
    context: QFAbvContext[object]
    state: QFAbvValuation[object]
    expression: TypedExpr

    def request(self) -> dict[str, Any]:
        values = [({"default": value.default, "entries": list(value.entries)}
                   if isinstance(value, QFAbvArrayValue) else value) for value in self.state.values]
        return {"declarations": [d.to_data() for d in self.context.declarations],
                "values": values, "expression": self.expression.to_data()}


@st.composite
def cases(draw, root_op: str):
    width = draw(st.sampled_from([1, 2, 3, 4, 8, 16, 32, 64]))
    iw = draw(st.integers(1, 4))
    bv, index, array = TermSort.bv(width), TermSort.bv(iw), TermSort.array(iw, width)
    declarations = tuple(Declaration(name, sort) for name, sort in
                         [("x", bv), ("y", bv), ("p", TermSort.bool()), ("q", TermSort.bool()), ("i", index), ("m", array)])
    context: QFAbvContext[object] = QFAbvContext(declarations)
    default = draw(numbers(width))
    raw_entries = draw(st.dictionaries(st.integers(0, (1 << iw) - 1), numbers(width), max_size=4))
    memory = QFAbvArrayValue(ArraySort(iw, width), default,
                           tuple(sorted((key, value) for key, value in raw_entries.items() if value != default)))
    values: tuple[Value, ...] = (draw(numbers(width)), draw(numbers(width)), draw(st.booleans()), draw(st.booleans()), draw(numbers(iw)), memory)
    state = QFAbvValuation(context, values)

    def bv_expr(w: int, depth: int = 2) -> TypedExpr:
        kinds = ["literal"]
        if w == width:
            kinds += ["x", "y"]
        if w == iw:
            kinds += ["i"]
        if depth:
            kinds += ["binary", "not", "ite"]
        kind = draw(st.sampled_from(kinds))
        if kind == "literal":
            return TypedExpr.bv_lit(w, draw(numbers(w)))
        if kind in {"x", "y", "i"}:
            return TypedExpr.var(kind, TermSort.bv(w))
        if kind == "not":
            return TypedExpr.unary("bv_not", bv_expr(w, depth - 1))
        if kind == "ite":
            return TypedExpr.ite(bool_expr(depth - 1), bv_expr(w, depth - 1), bv_expr(w, depth - 1))
        left = bv_expr(w, depth - 1)
        right = left if draw(st.booleans()) else bv_expr(w, depth - 1)
        return TypedExpr.binary(draw(st.sampled_from(BV_OPS)), left, right)

    def bool_expr(depth: int = 2) -> TypedExpr:
        kinds = ["literal", "p", "q"] + (["not", "binary", "compare"] if depth else [])
        kind = draw(st.sampled_from(kinds))
        if kind == "literal":
            return TypedExpr.bool_lit(draw(st.booleans()))
        if kind in {"p", "q"}:
            return TypedExpr.var(kind, TermSort.bool())
        if kind == "not":
            return TypedExpr.negate(bool_expr(depth - 1))
        if kind == "compare":
            return TypedExpr.binary(draw(st.sampled_from(CMP_OPS)), bv_expr(width, depth - 1), bv_expr(width, depth - 1))
        return TypedExpr.binary(draw(st.sampled_from(["bool_and", "bool_or", "eq"])), bool_expr(depth - 1), bool_expr(depth - 1))

    def array_expr(depth: int = 1) -> TypedExpr:
        kind = draw(st.sampled_from(["m", "constant"] + (["store"] if depth else [])))
        if kind == "m":
            return TypedExpr.var("m", array)
        if kind == "constant":
            return TypedExpr("const_array", array, (bv_expr(width, 1),))
        return TypedExpr("store", array, (array_expr(depth - 1), bv_expr(iw, 1), bv_expr(width, 1)))

    if root_op in BV_OPS + CMP_OPS:
        left = bv_expr(width)
        right = left if draw(st.booleans()) else bv_expr(width)
        expression = TypedExpr.binary(root_op, left, right)
    elif root_op == "var":
        declaration = draw(st.sampled_from(declarations))
        expression = TypedExpr.var(declaration.name, declaration.sort)
    elif root_op == "bool_lit":
        expression = TypedExpr.bool_lit(draw(st.booleans()))
    elif root_op == "bv_lit":
        expression = TypedExpr.bv_lit(width, draw(numbers(width)))
    elif root_op == "bool_not":
        expression = TypedExpr.negate(bool_expr())
    elif root_op in {"bool_and", "bool_or"}:
        expression = TypedExpr.binary(root_op, bool_expr(), bool_expr())
    elif root_op == "ite":
        choice = draw(st.sampled_from(["bool", "bv", "array"]))
        left, right = ((bool_expr(), bool_expr()) if choice == "bool" else
                       (bv_expr(width), bv_expr(width)) if choice == "bv" else (array_expr(), array_expr()))
        expression = TypedExpr.ite(bool_expr(), left, right)
    elif root_op == "eq":
        choice = draw(st.sampled_from(["bool", "bv", "array"]))
        left, right = ((bool_expr(), bool_expr()) if choice == "bool" else
                       (bv_expr(width), bv_expr(width)) if choice == "bv" else (array_expr(), array_expr()))
        expression = TypedExpr.equal(left, right)
    elif root_op == "bv_not":
        expression = TypedExpr.unary(root_op, bv_expr(width))
    elif root_op in {"zero_extend", "sign_extend"}:
        amount = draw(st.integers(1, 8))
        expression = TypedExpr(root_op, TermSort.bv(width + amount), (bv_expr(width),), amount=amount)
    elif root_op == "extract":
        low = draw(st.integers(0, width - 1))
        high = draw(st.integers(low, width - 1))
        expression = TypedExpr.extract(bv_expr(width), high, low)
    elif root_op == "concat":
        right_width = draw(st.integers(1, 64))
        expression = TypedExpr("concat", TermSort.bv(width + right_width), (bv_expr(width), bv_expr(right_width)))
    elif root_op == "const_array":
        expression = TypedExpr(root_op, array, (bv_expr(width),))
    elif root_op == "select":
        expression = TypedExpr.select(array_expr(), bv_expr(iw))
    elif root_op == "store":
        expression = TypedExpr(root_op, array, (array_expr(), bv_expr(iw), bv_expr(width)))
    else:
        raise AssertionError(root_op)
    return Case(context, state, expression)


def normalized(value: Value) -> dict[str, Any]:
    if isinstance(value, QFAbvArrayValue):
        entries = dict(value.entries)
        return {"kind": "array", "value": [entries.get(i, value.default) for i in range(1 << value.sort.index_width)]}
    return {"kind": "bool" if type(value) is bool else "bv", "value": value}


def boundary_cases():
    """Deterministic semantic edges; do not rely on random draws to hit them."""
    for width in [1, 2, 3, 4, 8, 16, 32, 64]:
        context: QFAbvContext[object] = QFAbvContext(())
        state = QFAbvValuation(context, ())
        mask = (1 << width) - 1
        def literal(value):
            return TypedExpr.bv_lit(width, value)
        for op in ["bv_udiv", "bv_sdiv", "bv_urem"]:
            for dividend in [0, 1, mask]:
                yield Case(context, state, TypedExpr.binary(op, literal(dividend), literal(0)))
        if width >= 4:
            negative_seven, negative_three = mask - 6, mask - 2
            for dividend, divisor in [(negative_seven, 3), (7, negative_three),
                                      (negative_seven, negative_three)]:
                yield Case(context, state, TypedExpr.binary(
                    "bv_sdiv", literal(dividend), literal(divisor)))
        yield Case(context, state, TypedExpr.binary(
            "bv_sdiv", literal(1 << (width - 1)), literal(mask)))
        for op in ["bv_shl", "bv_lshr", "bv_ashr"]:
            for amount in sorted({0, width - 1, width, width + 1, mask}):
                if amount <= mask:
                    for value in [1, mask]:
                        yield Case(context, state, TypedExpr.binary(op, literal(value), literal(amount)))
        for op, left, right in [("bv_add", mask, 1), ("bv_sub", 0, 1), ("bv_mul", mask, mask),
                                ("bv_slt", 1 << (width - 1), 0), ("bv_sle", mask, 0)]:
            yield Case(context, state, TypedExpr.binary(op, literal(left), literal(right)))
    context = QFAbvContext((Declaration("m", TermSort.array(2, 8)),))
    state = QFAbvValuation(context, (QFAbvArrayValue(ArraySort(2, 8), 7, ((1, 12),)),))
    memory = TypedExpr.var("m", TermSort.array(2, 8))
    for index in [0, 1, 3]:
        for value in [7, 12, 255]:
            stored = TypedExpr("store", memory.sort, (memory, TypedExpr.bv_lit(2, index), TypedExpr.bv_lit(8, value)))
            yield Case(context, state, stored)
            for read_index in [index, (index + 1) % 4]:
                yield Case(context, state, TypedExpr.select(stored, TypedExpr.bv_lit(2, read_index)))


class LeanOracle:
    """One persistent FFI process; isolate native aborts so Hypothesis can shrink."""
    def __init__(self, project: Path, artifacts: Path):
        self.project = project
        self.artifacts = artifacts
        self.process = None
        self.stderr = (artifacts / "lean-worker-stderr.log").open("a")

    def evaluate(self, request):
        if self.process is None or self.process.poll() is not None:
            self.process = subprocess.Popen(
                [sys.executable, __file__, "--bridge-project", str(self.project), "--worker"],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr, text=True)
        process = self.process
        try:
            process.stdin.write(json.dumps(request) + "\n")
            process.stdin.flush()
            if not select.select([process.stdout], [], [], 20)[0]:
                process.kill()
                process.wait()
                return {"error": "Lean evaluation timeout (20s)"}
            line = process.stdout.readline()
            if not line:
                process.wait()
                return {"error": "Lean FFI process exited", "exitcode": process.returncode}
            try:
                return json.loads(line)
            except json.JSONDecodeError:
                return {"error": "invalid Lean output", "output": line}
        except BrokenPipeError:
            process.wait()
            return {"error": "Lean FFI process exited", "exitcode": process.returncode}

    def close(self):
        if self.process is not None and self.process.poll() is None:
            self.process.stdin.close()
            self.process.wait(timeout=5)
        self.stderr.close()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-project", type=Path, required=True)
    parser.add_argument("--examples", type=int, default=200)
    parser.add_argument("--artifacts", type=Path, default=Path(".differential"))
    parser.add_argument("--worker", action="store_true")
    args = parser.parse_args()
    args.artifacts.mkdir(parents=True, exist_ok=True)
    if args.worker:
        library = LeanLibrary.from_lake(str(args.bridge_project.resolve()), "Bridge", build=False)
        for line in sys.stdin:
            print(library.evalJson(line.strip()), flush=True)
        return
    oracle = LeanOracle(args.bridge_project, args.artifacts)
    boundary_count = 0
    for case in boundary_cases():
        request = case.request()
        python_result = normalized(eval_expr(QFAbvExpr(case.context, decode_sort(case.expression.sort), case.expression), case.state))
        lean_result = oracle.evaluate(request)
        if python_result != lean_result:
            mismatch = {"request": request, "python": python_result, "lean": lean_result}
            (args.artifacts / "mismatch-boundary.json").write_text(json.dumps(mismatch, indent=2))
            oracle.close()
            raise AssertionError(mismatch)
        boundary_count += 1
    print(f"PASS explicit boundaries: {boundary_count}", flush=True)
    regression_count = 0
    for path in sorted((Path(__file__).parent / "regressions").glob("*.json")):
        regression = json.loads(path.read_text())
        request = regression["request"]
        context = QFAbvContext(tuple(Declaration.from_data(d) for d in request["declarations"]))
        values = tuple(
            QFAbvArrayValue(decode_sort(d.sort), value["default"], tuple(map(tuple, value["entries"])))
            if d.sort.kind == "array" else value
            for d, value in zip(context.declarations, request["values"]))
        state = QFAbvValuation(context, values)
        expression = TypedExpr.from_data(request["expression"])
        python_result = normalized(eval_expr(QFAbvExpr(context, decode_sort(expression.sort), expression), state))
        lean_result = oracle.evaluate(request)
        assert python_result == lean_result == regression["expected"], path
        regression_count += 1
    print(f"PASS saved regressions: {regression_count}", flush=True)
    counts: Counter[str] = Counter()
    failures: list[dict[str, Any]] = []
    for op in OPS:
        @settings(max_examples=args.examples, deadline=None,
                  database=DirectoryBasedExampleDatabase(args.artifacts / "hypothesis"))
        @given(cases(op))
        def check(case: Case) -> None:
            request = case.request()
            wrapped = QFAbvExpr(case.context, decode_sort(case.expression.sort), case.expression)
            python_result = normalized(eval_expr(wrapped, case.state))
            (args.artifacts / "last-request.json").write_text(json.dumps(request))
            lean_result = oracle.evaluate(request)
            counts[op] += 1
            if python_result != lean_result:
                # Hypothesis repeats this write while shrinking; the last request
                # is the minimized reproducer and both observed results.
                mismatch = {"operator": op, "request": request,
                            "python": python_result, "lean": lean_result}
                (args.artifacts / f"mismatch-{op}.json").write_text(json.dumps(mismatch, indent=2))
            assert python_result == lean_result, (op, request, python_result, lean_result)
        try:
            check()
            print(f"PASS {op}: {counts[op]} evaluations", flush=True)
        except Exception as exc:
            failures.append({"operator": op, "error": repr(exc)})
            print(f"FAIL {op}: {exc!r}", flush=True)
    summary = {"regression_cases": regression_count, "boundary_cases": boundary_count, "counts": dict(counts), "failures": failures,
               "widths": [1, 2, 3, 4, 8, 16, 32, 64], "array_index_widths": [1, 2, 3, 4]}
    (args.artifacts / "summary.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary), flush=True)
    oracle.close()
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
