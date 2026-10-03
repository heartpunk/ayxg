"""Exercise canonical Lean DAG output across BV/array and FP operator families."""
import argparse
import json
from pathlib import Path
from hypothesis import given, settings
from ayxg.codec import loads, typed_expr_roots_dag
from ayxg.eval import eval_expr
from ayxg.qfabv import QFAbvExpr, QFAbvContext, QFAbvValuation, decode_sort
from ayxg.fp import RoundingMode
from differential_expr import LeanOracle, OPS, cases
from differential_fp import OPS as FP_OPS, expression


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--bridge-project', type=Path, required=True)
    parser.add_argument('--artifacts', type=Path, required=True)
    args = parser.parse_args()
    args.artifacts.mkdir(parents=True, exist_ok=True)
    oracle = LeanOracle(args.bridge_project, args.artifacts)
    counts = {}

    def roundtrip(node, context):
        request = {'mode': 'roundtrip', 'declarations': [d.to_data() for d in context.declarations],
                   'expression_dag': typed_expr_roots_dag((node, node))}
        dag = oracle.evaluate(request)
        if 'error' in dag:
            raise RuntimeError(dag)
        restored = loads(json.dumps({'schema': 'ayxg-artifact-dag-v1', 'expression_dag': dag,
                                    'payload': [{'$expr': 0}, {'$expr': 1}]}))
        assert restored[0] is restored[1], 'shared roots must stay shared'
        assert dag == oracle.evaluate(dict(request, expression_dag=dag)), 'codec must be idempotent'
        return restored[0]

    try:
        # Oracle startup outside Hypothesis, so infrastructure errors do not shrink.
        from ayxg.expr import TypedExpr
        roundtrip(TypedExpr.bv_lit(8, 0), QFAbvContext(()))
        # 81 distinct nodes but 2**80 tree paths: identity caching is essential.
        shared = TypedExpr.bv_lit(8, 1)
        for _ in range(80):
            shared = TypedExpr.binary('bv_add', shared, shared)
        shared_dag = typed_expr_roots_dag((shared, shared))
        exported = oracle.evaluate({'mode': 'roundtrip', 'declarations': [],
                                     'expression_dag': shared_dag})
        assert exported == shared_dag
        assert len(exported['nodes']) == 81
        counts['doubling_dag_depth_80'] = 1
        polymorphic = oracle.evaluate({'mode': 'writer_polymorphic'})
        values = loads(json.dumps({'schema': 'ayxg-artifact-dag-v1',
            'expression_dag': polymorphic, 'payload': [{'$expr':0}, {'$expr':1}]}))
        empty = QFAbvContext(())
        assert [eval_expr(QFAbvExpr(empty, decode_sort(v.sort), v),
                         QFAbvValuation(empty, ())) for v in values] == [True, 7]
        counts['polymorphic_variable_sorts'] = 1
        for op in OPS:
            @given(cases(op))
            @settings(max_examples=10, derandomize=True, deadline=None)
            def check(case):
                restored = roundtrip(case.expression, case.context)
                sort = decode_sort(case.expression.sort)
                assert eval_expr(QFAbvExpr(case.context, sort, restored), case.state) == eval_expr(
                    QFAbvExpr(case.context, sort, case.expression), case.state)
                counts[op] = counts.get(op, 0) + 1
            check()
        context = QFAbvContext(())
        state = QFAbvValuation(context, ())
        for op in FP_OPS:
            for mode in RoundingMode:
                node = expression(op, 8, 24, 0x3f800000, 0x40000000, 0x40400000, mode)
                restored = roundtrip(node, context)
                sort = decode_sort(node.sort)
                assert eval_expr(QFAbvExpr(context, sort, restored), state) == eval_expr(
                    QFAbvExpr(context, sort, node), state)
                counts[op] = counts.get(op, 0) + 1
    finally:
        oracle.close()
    (args.artifacts / 'coverage.json').write_text(json.dumps({'status': 'PASS', 'counts': counts}, indent=2))
    print(f'{sum(counts.values())} operator codec round trips passed', flush=True)


if __name__ == '__main__':
    main()
