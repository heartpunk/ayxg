"""Differential transition checks through the actual AYXG Lean FFI bridge."""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path

from hypothesis import given, settings, strategies as st
from hypothesis.database import DirectoryBasedExampleDatabase

from ayxg import (Declaration, QFAbvContext, QFAbvExpr, QFAbvStep,
                  QFAbvUpdate, QFAbvValuation, TermSort, TypedExpr,
                  eval_step, eval_update)
from ayxg.qfabv import ArraySort, BoolSort, QFAbvArrayValue, decode_sort
from differential_expr import BV_OPS, CMP_OPS, LeanOracle, normalized, numbers


def wrap(context, node):
    return QFAbvExpr(context, decode_sort(node.sort), node)


def state_result(state):
    return None if state is None else [normalized(value) for value in state.values]


def values_data(state):
    return [({"default": v.default, "entries": list(v.entries)}
             if isinstance(v, QFAbvArrayValue) else v) for v in state.values]


def step_data(step):
    return {"guard": step.guard.node.to_data(),
            "rhs": [e.node.to_data() for e in step.update.rhs]}


@dataclass
class TransitionCase:
    state: QFAbvValuation
    left: QFAbvStep
    right: QFAbvStep

    def request(self):
        return {"mode": "transition",
                "declarations": [d.to_data() for d in self.state.context.declarations],
                "values": values_data(self.state),
                "middle": [d.to_data() for d in self.left.update.target.declarations],
                "output": [d.to_data() for d in self.right.update.target.declarations],
                "left": step_data(self.left), "right": step_data(self.right)}

    def python_result(self):
        first = eval_step(self.left, self.state)
        sequential = None if first is None else eval_step(self.right, first)
        identity = QFAbvStep.identity(self.state.context)
        update_first = eval_update(self.left.update, self.state)
        return {"update": state_result(update_first),
                "update_composed": state_result(eval_update(self.left.update.compose(self.right.update), self.state)),
                "update_sequential": state_result(eval_update(self.right.update, update_first)),
                "step": state_result(first),
                "composed": state_result(eval_step(self.left.compose(self.right), self.state)),
                "sequential": state_result(sequential),
                "identity_update": state_result(eval_update(QFAbvUpdate.identity(self.state.context), self.state)),
                "identity_step": state_result(eval_step(identity, self.state)),
                "identity_left": state_result(eval_step(identity.compose(self.left), self.state)),
                "identity_right": state_result(eval_step(self.left.compose(QFAbvStep.identity(self.left.update.target)), self.state))}


@st.composite
def transition_cases(draw, mode):
    width = draw(st.sampled_from([1, 2, 4, 8, 16, 32, 64]))
    iw = draw(st.integers(1, 4))
    pool = [TermSort.bool(), TermSort.bv(width), TermSort.bv(iw), TermSort.array(iw, width)]
    def context():
        # Reusing names across stages with independently chosen sorts probes
        # simultaneous substitution rather than accidental name-based writes.
        names = draw(st.lists(st.sampled_from(["x", "y", "p", "m", "i"]), unique=True, max_size=5))
        return QFAbvContext(tuple(Declaration(name, draw(st.sampled_from(pool))) for name in names))
    source = context()
    middle = source if mode == "homogeneous" else context()
    output = source if mode == "homogeneous" else context()

    def expression(ctx, sort, depth=2):
        candidates = [d for d in ctx.declarations if d.sort == sort]
        options = ["literal"] + (["var"] if candidates else [])
        if depth:
            options += ["ite"]
            options += (["not", "boolbin", "compare"] if sort.kind == "bool" else
                        ["binary", "not", "select", "reshape"] if sort.kind == "bv" else ["store"])
        kind = draw(st.sampled_from(options))
        if kind == "var":
            d = draw(st.sampled_from(candidates))
            return TypedExpr.var(d.name, sort)
        if kind == "literal":
            if sort.kind == "bool":
                return TypedExpr.bool_lit(draw(st.booleans()))
            if sort.kind == "bv":
                return TypedExpr.bv_lit(sort.width, draw(numbers(sort.width)))
            return TypedExpr("const_array", sort, (TypedExpr.bv_lit(sort.value_width, draw(numbers(sort.value_width))),))
        if kind == "ite":
            return TypedExpr.ite(expression(ctx, TermSort.bool(), depth-1),
                                 expression(ctx, sort, depth-1), expression(ctx, sort, depth-1))
        if kind == "not":
            return TypedExpr.unary("bool_not" if sort.kind == "bool" else "bv_not", expression(ctx, sort, depth-1))
        if kind in {"binary", "boolbin"}:
            left = expression(ctx, sort, depth-1)
            right = left if draw(st.booleans()) else expression(ctx, sort, depth-1)
            return TypedExpr.binary(draw(st.sampled_from(BV_OPS if kind == "binary" else ["bool_and", "bool_or", "eq"])), left, right)
        if kind == "compare":
            bv = TermSort.bv(width)
            return TypedExpr.binary(draw(st.sampled_from(CMP_OPS)), expression(ctx, bv, depth-1), expression(ctx, bv, depth-1))
        if kind == "reshape":
            # Both extension and extraction can bridge differing context widths.
            if sort.width > 1 and draw(st.booleans()):
                w = draw(st.integers(1, sort.width-1))
                return TypedExpr(draw(st.sampled_from(["zero_extend", "sign_extend"])), sort,
                                 (expression(ctx, TermSort.bv(w), depth-1),), amount=sort.width-w)
            w = sort.width + draw(st.integers(1, 4))
            return TypedExpr.extract(expression(ctx, TermSort.bv(w), depth-1), sort.width-1, 0)
        if kind == "select":
            array = TermSort.array(iw, sort.width)
            return TypedExpr.select(expression(ctx, array, depth-1), expression(ctx, TermSort.bv(iw), depth-1))
        return TypedExpr("store", sort, (expression(ctx, sort, depth-1),
                         expression(ctx, TermSort.bv(sort.index_width), depth-1),
                         expression(ctx, TermSort.bv(sort.value_width), depth-1)))

    def value(sort):
        if sort.kind == "bool":
            return draw(st.booleans())
        if sort.kind == "bv":
            return draw(numbers(sort.width))
        default = draw(numbers(sort.value_width))
        entries = draw(st.dictionaries(st.integers(0, (1 << sort.index_width)-1), numbers(sort.value_width), max_size=4))
        return QFAbvArrayValue(ArraySort(sort.index_width, sort.value_width), default,
                              tuple(sorted((i,v) for i,v in entries.items() if v != default)))
    state = QFAbvValuation(source, tuple(value(d.sort) for d in source.declarations))
    def step(a,b, forced=None):
        guard = expression(a, TermSort.bool()) if forced is None else TypedExpr.bool_lit(forced)
        update = QFAbvUpdate(a,b,tuple(wrap(a,expression(a,d.sort)) for d in b.declarations))
        return QFAbvStep(QFAbvExpr(a,BoolSort(),guard),update)
    left_forced = False if mode == "disabled_left" else True if mode in {"enabled", "disabled_right"} else None
    right_forced = False if mode == "disabled_right" else True if mode == "enabled" else None
    return TransitionCase(state,step(source,middle,left_forced),step(middle,output,right_forced))


def explicit_cases():
    # All RHSs must see old values; the second guard must see the swapped state.
    for width in [1,2,8,32,64]:
        bv = TermSort.bv(width)
        ctx = QFAbvContext((Declaration("x",bv),Declaration("y",bv)))
        x,y = TypedExpr.var("x",bv),TypedExpr.var("y",bv)
        swap = QFAbvUpdate(ctx,ctx,(wrap(ctx,y),wrap(ctx,x)))
        state = QFAbvValuation(ctx,(0,1))
        left = QFAbvStep(wrap(ctx,TypedExpr.bool_lit(True)),swap)
        for expected in [0,1]:
            guard = TypedExpr.equal(x,TypedExpr.bv_lit(width,expected))
            right = QFAbvStep(wrap(ctx,guard),QFAbvUpdate.identity(ctx))
            yield TransitionCase(state,left,right), {"update": [normalized(1),normalized(0)],
                "composed": [normalized(1),normalized(0)] if expected == 1 else None}
    # Explicit store/read aliasing and a renamed, heterogeneous final context.
    arr,bv = TermSort.array(2,8),TermSort.bv(8)
    src = QFAbvContext((Declaration("m",arr),Declaration("x",bv)))
    mid = QFAbvContext((Declaration("x",bv),Declaration("m",arr)))
    out = QFAbvContext((Declaration("result",bv),))
    m = TypedExpr.var("m",arr)
    x = TypedExpr.var("x",bv)
    stored = TypedExpr("store",arr,(m,TypedExpr.bv_lit(2,1),x))
    for old in [0,255]:
        state = QFAbvValuation(src,(QFAbvArrayValue(ArraySort(2,8),old),7))
        left = QFAbvStep(wrap(src,TypedExpr.bool_lit(True)),QFAbvUpdate(src,mid,(wrap(src,TypedExpr.bv_lit(8,9)),wrap(src,stored))))
        read = TypedExpr.select(TypedExpr.var("m",arr),TypedExpr.bv_lit(2,1))
        right = QFAbvStep(wrap(mid,TypedExpr.equal(read,TypedExpr.bv_lit(8,7))),QFAbvUpdate(mid,out,(wrap(mid,read),)))
        yield TransitionCase(state,left,right), {"composed": [normalized(7)]}


def check(case, oracle, artifacts, lane, counts, coverage, expected=None):
    request = case.request()
    (artifacts / "last-transition-request.json").write_text(json.dumps(request))
    python = case.python_result()
    lean = oracle.evaluate(request)
    counts[lane] += 1
    coverage["enabled_left" if python["step"] is not None else "disabled_left"] += 1
    coverage["enabled_composition" if python["composed"] is not None else "disabled_composition"] += 1
    if python["step"] is not None and python["composed"] is None:
        coverage["disabled_right_after_enabled_left"] += 1
    contexts = [case.state.context, case.left.update.target, case.right.update.target]
    if contexts[0] != contexts[1] or contexts[1] != contexts[2]:
        coverage["heterogeneous"] += 1
    if any(not c.declarations for c in contexts):
        coverage["empty_context"] += 1
    if any(d.sort.kind == "array" for c in contexts for d in c.declarations):
        coverage["array_context"] += 1
    for a,b in zip(contexts,contexts[1:]):
        previous = {d.name:d.sort for d in a.declarations}
        if any(d.name in previous and previous[d.name] != d.sort for d in b.declarations):
            coverage["same_name_changed_sort"] += 1
    seen = set()
    stack = [case.left.guard.node, case.right.guard.node,
             *(e.node for e in case.left.update.rhs), *(e.node for e in case.right.update.rhs)]
    while stack:
        node = stack.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        coverage["op:" + node.op] += 1
        stack.extend(node.args)
    checks = {"differential": python == lean,
              "update_sequence": python["update_composed"] == python["update_sequential"],
              "step_sequence": python["composed"] == python["sequential"],
              "identity_update": python["identity_update"] == state_result(case.state),
              "identity_step": python["identity_step"] == state_result(case.state),
              "identity_left": python["identity_left"] == python["step"],
              "identity_right": python["identity_right"] == python["step"]}
    if expected:
        checks["explicit_expected"] = all(python[k] == v for k,v in expected.items())
    if not all(checks.values()):
        mismatch = {"lane":lane,"request":request,"python":python,"lean":lean,"checks":checks}
        (artifacts / f"mismatch-{lane}.json").write_text(json.dumps(mismatch,indent=2))
        raise AssertionError(mismatch)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-project",type=Path,required=True)
    parser.add_argument("--examples",type=int,default=200)
    parser.add_argument("--artifacts",type=Path,default=Path(".transition-differential"))
    args = parser.parse_args()
    args.artifacts.mkdir(parents=True,exist_ok=True)
    oracle = LeanOracle(args.bridge_project,args.artifacts)
    counts = Counter()
    coverage = Counter()
    failures = []
    try:
        for case,expected in explicit_cases():
            check(case,oracle,args.artifacts,"explicit",counts,coverage,expected)
        print(f"PASS explicit: {counts['explicit']}",flush=True)
        for lane in ["homogeneous","heterogeneous","enabled","disabled_left","disabled_right"]:
            @settings(max_examples=args.examples,deadline=None,
                      database=DirectoryBasedExampleDatabase(args.artifacts / "hypothesis"))
            @given(transition_cases(lane))
            def test(case):
                check(case,oracle,args.artifacts,lane,counts,coverage)
            try:
                test()
                print(f"PASS {lane}: {counts[lane]}",flush=True)
            except Exception as exc:
                failures.append({"lane":lane,"error":repr(exc)})
                print(f"FAIL {lane}: {exc!r}",flush=True)
    finally:
        oracle.close()
        summary = {"counts":dict(counts),"coverage":dict(coverage),"failures":failures,
                   "checks_per_case":10,"array_index_widths":[1,2,3,4],
                   "bv_widths":[1,2,4,8,16,32,64]}
        (args.artifacts / "summary.json").write_text(json.dumps(summary,indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
