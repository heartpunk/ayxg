"""Direct Lean/Python/Z3 checks for positional parallel-let expressions."""
import argparse
import json
from pathlib import Path
from hypothesis import given, settings, strategies as st
import z3
from ayxg.expr import Declaration, TermSort, TypedExpr as E
from ayxg.qfabv import QFAbvContext, QFAbvValuation, QFAbvExpr, decode_sort
from ayxg.eval import eval_expr
from ayxg.codec import dumps, loads, typed_expr_roots_dag
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
            E.let_par((Declaration('b', TermSort.bool()),), (E.bool_lit(x < y),),
                E.ite(E.at(0,TermSort.bool()), E.bv_lit(8,1), E.bv_lit(8,0))),
            E.let_par((Declaration('m', TermSort.array(2,8)),),
                (E('const_array',TermSort.array(2,8),(E.bv_lit(8,x),)),),
                E.select(E.at(0,TermSort.array(2,8)), E.bv_lit(2,y%4))),
            E.let_par((Declaration('r',TermSort.rounding_mode()),),
                (E('rm_lit',TermSort.rounding_mode(),value='RNA'),),
                E.ite(E.equal(E.at(0,TermSort.rounding_mode()), E('rm_lit',TermSort.rounding_mode(),value='RNA')),E.bv_lit(8,1),E.bv_lit(8,0))),
            E.let_par((Declaration('f',TermSort.fp(8,24)),),
                (E('bv_to_fp',TermSort.fp(8,24),(E.bv_lit(32,0x3f800000),)),),
                E.ite(E.equal(E.at(0,TermSort.fp(8,24)), E.at(0,TermSort.fp(8,24))),E.bv_lit(8,1),E.bv_lit(8,0))),
        ]
        for node in examples:
            node = loads(dumps(node))
            py = eval_expr(QFAbvExpr(ctx, decode_sort(bv), node), QFAbvValuation(ctx,(x,y)))
            request = {'declarations':[d.to_data(),d.to_data()], 'values':[x,y], 'expression_dag':typed_expr_roots_dag((node,))}
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
    (args.artifacts/'coverage.json').write_text(json.dumps({'comparisons':total,'families':8,'status':'PASS'},indent=2))
    print(f'{total} Lean/Python/Z3 binding comparisons passed')

if __name__ == '__main__': main()
