"""Bounded segment differential tests; exploration is test-only, not an API."""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
import json
from pathlib import Path
from hypothesis import given, settings, strategies as st
from hypothesis.database import DirectoryBasedExampleDatabase
from ayxg import (Adapter, Declaration, QFAbvContext, QFAbvStep, QFAbvUpdate,
                  QFAbvValuation, Segment, SegmentDAG, SegmentNode, STS,
                  TypedExpr, TermSort, eval_step)
from ayxg.substitution import substitute_exprs
from differential_expr import LeanOracle
from differential_transition import transition_cases, wrap, step_data, values_data, state_result


def output_set(outputs):
    return sorted(set(json.dumps(o,sort_keys=True) for o in outputs))


def explore(segment,state,fuel):
    first = eval_step(segment.input.label,state)
    frontier = [] if first is None else [first]
    outputs = []
    for _ in range(fuel+1):
        for state in frontier:
            for exit in segment.exits:
                result = eval_step(exit.label,state)
                if result is not None:
                    outputs.append(state_result(result))
        frontier = [result for state in frontier for step in segment.body.steps
                    if (result := eval_step(step,state)) is not None]
    return outputs


@dataclass
class Case:
    segment: Segment
    state: QFAbvValuation
    fuel: int
    target_context: QFAbvContext | None = None

    def request(self):
        entry = self.segment.input.label
        # Output context remains known even when there are zero exit adapters.
        return {"mode":"segment","declarations":[d.to_data() for d in self.state.context.declarations],
                "values":values_data(self.state),
                "body_context":[d.to_data() for d in entry.update.target.declarations],
                "output":[d.to_data() for d in self.output_context.declarations],
                "entry":step_data(entry),"steps":[step_data(s) for s in self.segment.body.steps],
                "exits":[step_data(e.label) for e in self.segment.exits],"fuel":self.fuel}

    @property
    def output_context(self):
        if self.target_context is not None:
            return self.target_context
        body = self.segment.input.label.update.target
        return QFAbvContext(tuple(Declaration("out_"+d.name,d.sort) for d in reversed(body.declarations)))


@st.composite
def cases(draw,fuel,lane):
    base = draw(transition_cases("homogeneous"))
    body = base.state.context
    source = QFAbvContext(tuple(Declaration("in_"+d.name,d.sort) for d in body.declarations))
    state = QFAbvValuation(source,base.state.values)
    replacements = {d.name:TypedExpr.var("in_"+d.name,d.sort) for d in body.declarations}
    nodes = substitute_exprs((base.left.guard.node,*(e.node for e in base.left.update.rhs)),replacements)
    guard = TypedExpr.bool_lit(False) if lane == "disabled_entry" else TypedExpr.bool_lit(True) if lane in {"enabled", "mixed_exits"} else nodes[0]
    entry = QFAbvStep(wrap(source,guard),QFAbvUpdate(source,body,tuple(wrap(source,n) for n in nodes[1:])))
    steps = (base.left,base.right)
    if lane in {"enabled", "mixed_exits"}:
        steps = tuple(QFAbvStep(wrap(body,TypedExpr.bool_lit(True)),s.update) for s in steps)
    target = QFAbvContext(tuple(Declaration("out_"+d.name,d.sort) for d in reversed(body.declarations)))
    exits = []
    exit_count = draw(st.integers(0,2)) if lane == "random" else 2
    for exit_index in range(exit_count):
        # Different adapters must denote different relations. Keep the first
        # projection and perturb numeric outputs on later exits.
        guard = (TypedExpr.bool_lit(False) if lane == "disabled_exit" or (lane == "mixed_exits" and exit_index == 0)
                 else TypedExpr.bool_lit(True) if lane in {"enabled", "mixed_exits"} else base.right.guard.node)
        projected = tuple(reversed(base.right.update.rhs))
        rhs = []
        for declaration, value_expr in zip(target.declarations, projected):
            node = value_expr.node
            if exit_index and declaration.sort.kind == "bv":
                node = TypedExpr.binary("bv_add", node, TypedExpr.bv_lit(declaration.sort.width, exit_index))
            rhs.append(wrap(body, node))
        update = QFAbvUpdate(body,target,tuple(rhs))
        exits.append(Adapter(QFAbvStep(wrap(body,guard),update)))
    return Case(Segment(Adapter(entry),STS(steps),tuple(exits)),state,fuel)


def check(case,oracle,artifacts,lane,counts,coverage,known=None):
    request = case.request()
    (artifacts / "last-segment-request.json").write_text(json.dumps(request))
    direct = output_set(explore(case.segment,case.state,case.fuel))
    dag = SegmentDAG((SegmentNode(0,case.segment),SegmentNode(1,case.segment,(0,)),
                      SegmentNode(2,case.segment,(0,))),(1,2))
    by_key = {node.key:node for node in dag.nodes}
    shared = [output_set(explore(by_key[key].segment,case.state,case.fuel))
              for root in dag.roots for key in by_key[root].children]
    lean = oracle.evaluate(request)
    observed = {"direct":output_set(lean["direct"]),"shared":[output_set(o) for o in lean["shared"]]} if "direct" in lean else lean
    expected = {"direct":direct,"shared":shared}
    counts[lane] += 1
    coverage[f"fuel:{case.fuel}"] += 1
    coverage["nonempty_outputs" if direct else "empty_outputs"] += 1
    if any(d.sort.kind == "array" for d in case.state.context.declarations):
        coverage["arrays"] += 1
    if not case.segment.exits:
        coverage["no_exits"] += 1
    if len(direct) > 1:
        coverage["multiple_distinct_outputs"] += 1
    if len(case.segment.exits) > 1 and len({e.label.update.rhs for e in case.segment.exits}) > 1:
        coverage["distinct_exit_relations"] += 1
    if (observed != expected or shared != [direct,direct]
            or (lane.startswith("disabled") and direct)
            or (lane == "mixed_exits" and not direct)
            or (known is not None and direct != known)):
        mismatch = {"request":request,"python":expected,"lean":observed}
        (artifacts / f"mismatch-{lane}.json").write_text(json.dumps(mismatch,indent=2))
        raise AssertionError(mismatch)


def explicit_cases():
    bv = TermSort.bv(8)
    source = QFAbvContext((Declaration("in_x",bv),))
    body = QFAbvContext((Declaration("x",bv),))
    output = QFAbvContext((Declaration("out_x",bv),))
    entry = QFAbvStep(wrap(source,TypedExpr.bool_lit(True)),
        QFAbvUpdate(source,body,(wrap(source,TypedExpr.var("in_x",bv)),)))
    x = TypedExpr.var("x",bv)
    steps = tuple(QFAbvStep(wrap(body,TypedExpr.bool_lit(True)),
        QFAbvUpdate(body,body,(wrap(body,TypedExpr.binary("bv_add",x,TypedExpr.bv_lit(8,n))),))) for n in [1,2])
    exit = QFAbvStep(wrap(body,TypedExpr.bool_lit(True)),QFAbvUpdate(body,output,(wrap(body,x),)))
    segment = Segment(Adapter(entry),STS(steps),(Adapter(exit),))
    for fuel in range(4):
        yield Case(segment,QFAbvValuation(source,(0,)),fuel), output_set(
            [[{"kind":"bv","value":n}] for n in range(2*fuel+1)])
    # Empty body supports zero-step exits; no exits gives the empty relation.
    yield Case(Segment(Adapter(entry),STS(()),(Adapter(exit),)),QFAbvValuation(source,(9,)),3), output_set([[{"kind":"bv","value":9}]])
    # Distinct enabled output adapters contribute distinct results.
    plus_one = QFAbvStep(wrap(body,TypedExpr.bool_lit(True)),
        QFAbvUpdate(body,output,(wrap(body,TypedExpr.binary("bv_add",x,TypedExpr.bv_lit(8,1))),)))
    yield Case(Segment(Adapter(entry),STS(()),(Adapter(exit),Adapter(plus_one))),
        QFAbvValuation(source,(9,)),0), output_set([
            [{"kind":"bv","value":9}], [{"kind":"bv","value":10}]])
    yield Case(Segment(Adapter(entry),STS((steps[0],)),()),QFAbvValuation(source,(9,)),3), []
    disabled_entry = QFAbvStep(wrap(source,TypedExpr.bool_lit(False)),entry.update)
    yield Case(Segment(Adapter(disabled_entry),STS((steps[0],)),(Adapter(exit),)),
        QFAbvValuation(source,(9,)),1), []
    disabled_exit = QFAbvStep(wrap(body,TypedExpr.bool_lit(False)),exit.update)
    yield Case(Segment(Adapter(entry),STS((steps[0],)),(Adapter(disabled_exit),)),
        QFAbvValuation(source,(9,)),1), []
    # A self-loop remains bounded by the chosen run length.
    loop = QFAbvStep(wrap(body,TypedExpr.bool_lit(True)),
        QFAbvUpdate(body,body,(wrap(body,TypedExpr.binary("bv_add",x,TypedExpr.bv_lit(8,1))),)))
    yield Case(Segment(Adapter(entry),STS((loop,)),(Adapter(exit),)),QFAbvValuation(source,(9,)),3), output_set(
        [[{"kind":"bv","value":n}] for n in [9,10,11,12]])
    # A genuinely heterogeneous interface: two input fields, three body
    # fields (including an array), and one renamed output field.
    source2 = QFAbvContext((Declaration("src_pc",bv),Declaration("src_flag",TermSort.bool())))
    body2 = QFAbvContext((Declaration("pc",bv),Declaration("flag",TermSort.bool()),
                          Declaration("mem",TermSort.array(2,8))))
    target2 = QFAbvContext((Declaration("dst_pc",bv),))
    initial_memory = TypedExpr("const_array",TermSort.array(2,8),(TypedExpr.bv_lit(8,0),))
    entry_rhs = (
        wrap(source2,TypedExpr.var("src_pc",bv)),
        wrap(source2,TypedExpr.var("src_flag",TermSort.bool())),
        wrap(source2,initial_memory))
    entry2 = QFAbvStep(wrap(source2,TypedExpr.bool_lit(True)),
        QFAbvUpdate(source2,body2,entry_rhs))
    pc = TypedExpr.var("pc",bv)
    advance2 = QFAbvStep(wrap(body2,TypedExpr.bool_lit(True)),QFAbvUpdate(body2,body2,(
        wrap(body2,TypedExpr.binary("bv_add",pc,TypedExpr.bv_lit(8,1))),
        wrap(body2,TypedExpr.var("flag",TermSort.bool())),
        wrap(body2,TypedExpr.var("mem",TermSort.array(2,8))))))
    exit2 = QFAbvStep(wrap(body2,TypedExpr.bool_lit(True)),QFAbvUpdate(body2,target2,
        (wrap(body2,pc),)))
    yield Case(Segment(Adapter(entry2),STS((advance2,)),(Adapter(exit2),)),
        QFAbvValuation(source2,(5,True)),1,target2), output_set([
            [{"kind":"bv","value":5}], [{"kind":"bv","value":6}]])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bridge-project",type=Path,required=True)
    parser.add_argument("--examples",type=int,default=100)
    parser.add_argument("--artifacts",type=Path,required=True)
    args = parser.parse_args()
    args.artifacts.mkdir(parents=True,exist_ok=True)
    oracle = LeanOracle(args.bridge_project,args.artifacts)
    counts,coverage,failures = Counter(),Counter(),[]
    try:
        for case,known in explicit_cases():
            check(case,oracle,args.artifacts,"explicit",counts,coverage,known)
        print("PASS explicit branching, zero-step, distinct exits, disabled adapters, no-exit, and cycle cases",flush=True)
        for lane in ["random","enabled","disabled_entry","disabled_exit","mixed_exits"]:
            for fuel in range(4):
                name = f"{lane}-{fuel}"
                @settings(max_examples=args.examples,deadline=None,
                          database=DirectoryBasedExampleDatabase(args.artifacts / "hypothesis"))
                @given(cases(fuel,lane))
                def test(case):
                    check(case,oracle,args.artifacts,lane,counts,coverage)
                try:
                    test()
                    print(f"PASS {name}",flush=True)
                except Exception as exc:
                    failures.append({"lane":name,"error":repr(exc)})
                    print(f"FAIL {name}: {exc!r}",flush=True)
    finally:
        oracle.close()
        (args.artifacts / "summary.json").write_text(json.dumps({"counts":dict(counts),
            "coverage":dict(coverage),"failures":failures,"max_body_transitions":3,
            "scope":"test-only bounded exploration over actual segment data and primitive evaluators; not a proof of unbounded Segment.denotes"},indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
