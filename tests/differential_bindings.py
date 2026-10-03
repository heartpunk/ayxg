"""Direct Lean/Python/Z3 checks for positional parallel-let expressions."""
import argparse
import json
from pathlib import Path
from hypothesis import given, settings, strategies as st
import z3
from ayxg.expr import Declaration, TermSort, TypedExpr as E
from ayxg.qfabv import QFAbvContext, QFAbvValuation, QFAbvExpr, decode_sort
from ayxg.eval import eval_expr
from ayxg.codec import dumps, loads
from ayxg.z3 import expr_to_z3
from differential_expr import LeanOracle

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--bridge-project', type=Path, required=True)
    p.add_argument('--artifacts', type=Path, required=True)
    args = p.parse_args()
    args.artifacts.mkdir(parents=True, exist_ok=True)
    oracle = LeanOracle(args.bridge_project, args.artifacts)
    bv = TermSort.bv(8)
    d = Declaration('x', bv)
    ctx = QFAbvContext((d, d))
    total = 0
    @given(st.integers(0,255), st.integers(0,255))
    @settings(max_examples=80, derandomize=True, deadline=None)
    def check(x, y):
        nonlocal total
        shared = E.at(0, bv)
        examples = [
            E.let_par((d,d), (E.bv_lit(8,x), E.at(1,bv)), E.at(1,bv)),
            E.let_par((d,), (E.bv_lit(8,x),), E.let_par((d,), (E.bv_lit(8,y),), E.at(1,bv))),
            E.binary('bv_add', E.let_par((d,), (E.bv_lit(8,x),), shared), E.let_par((d,), (E.bv_lit(8,y),), shared)),
            E.let_par((), (), E.at(1,bv)),
        ]
        for node in examples:
            node = loads(dumps(node))
            py = eval_expr(QFAbvExpr(ctx, decode_sort(bv), node), QFAbvValuation(ctx,(x,y)))
            request = {'declarations':[d.to_data(),d.to_data()], 'values':[x,y], 'expression':node.to_data()}
            lean = oracle.evaluate(request)
            expected = {'kind':'bv', 'value':py}
            zctx = z3.Context()
            solver = z3.simplify(expr_to_z3(node, [('x',z3.BitVecVal(x,8,zctx)),('x',z3.BitVecVal(y,8,zctx))], zctx)).as_long()
            if lean != expected or solver != py:
                (args.artifacts/'counterexample.json').write_text(json.dumps({'request':request,'python':py,'lean':lean,'z3':solver},indent=2))
                raise AssertionError((py,lean,solver))
            total += 1
    try:
        check()
    finally:
        if oracle.process is not None and oracle.process.poll() is None:
            oracle.process.stdin.close()
            oracle.process.wait(timeout=20)
        oracle.stderr.close()
    (args.artifacts/'coverage.json').write_text(json.dumps({'comparisons':total,'families':4,'status':'PASS'},indent=2))
    print(f'{total} Lean/Python/Z3 binding comparisons passed')

if __name__ == '__main__': main()
