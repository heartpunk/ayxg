"""Parallel-let/positional contracts, shared scopes, and substitution laws."""
import pytest
from hypothesis import given, settings, strategies as st
import z3
from ayxg.expr import Declaration, TermSort, TypedExpr as E, ArtifactError
from ayxg.qfabv import QFAbvContext, QFAbvExpr, QFAbvValuation, QFAbvUpdate, decode_sort
from ayxg.eval import eval_expr, eval_update
from ayxg.substitution import substitute_exprs
from ayxg.codec import dumps, loads
from ayxg.z3 import expr_to_z3

B = TermSort.bv(8)
D = Declaration('x', B)

def evaluate(node, values=(), declarations=()):
    context = QFAbvContext(declarations)
    return eval_expr(QFAbvExpr(context, decode_sort(node.sort), node), QFAbvValuation(context, values))


def test_parallel_rhs_see_old_context():
    node = E.let_par((D, D), (E.bv_lit(8, 1), E.at(0, B)), E.at(1, B))
    assert evaluate(node, (9,), (D,)) == 9
    assert evaluate(E.let_par((), (), E.at(0, B)), (9,), (D,)) == 9


def test_nested_binding_and_shadowed_outer_reference():
    # inner slot1 still selects outer x despite identical names.
    node = E.let_par((D,), (E.bv_lit(8, 7),),
        E.let_par((D,), (E.bv_lit(8, 3),), E.at(1, B)))
    assert evaluate(node) == 7
    named = E.let_par((D,), (E.bv_lit(8, 7),), E.var('x', B))
    assert evaluate(named) == 7


def test_same_dag_node_different_scopes_and_codec():
    body = E.at(0, B)
    left = E.let_par((D,), (E.bv_lit(8, 2),), body)
    right = E.let_par((D,), (E.bv_lit(8, 8),), body)
    node = E.binary('bv_add', left, right)
    decoded = loads(dumps(node))
    assert decoded.args[0].args[-1] is decoded.args[1].args[-1]
    assert evaluate(decoded) == 10
    assert E.from_data(node.to_data()) == node
    ctx = z3.Context()
    assert z3.simplify(expr_to_z3(decoded, {}, ctx)).as_long() == 10


def test_substitution_avoids_named_capture():
    node = E.let_par((D,), (E.bv_lit(8, 1),), E.var('y', B))
    replaced, = substitute_exprs((node,), {'y': E.var('x', B)})
    assert evaluate(replaced, (17,), (D,)) == 17


def test_substitution_shifts_positional_replacements():
    node = E.let_par((D,), (E.bv_lit(8, 1),), E.at(1, B))
    replaced, = substitute_exprs((node,), {}, positional=(E.at(0, B),))
    assert evaluate(replaced, (17,), (D,)) == 17


def test_context_duplicate_names_have_distinct_positions():
    context = QFAbvContext((D, D))
    state = QFAbvValuation(context, (3, 9))
    assert eval_update(QFAbvUpdate.identity(context), state) == state
    assert evaluate(E.at(1, B), (3, 9), (D, D)) == 9
    assert evaluate(E.var('x', B), (3, 9), (D, D)) == 3


def test_binding_errors():
    with pytest.raises(ArtifactError):
        E.let_par((D,), (E.bool_lit(True),), E.at(0, B))
    with pytest.raises(ArtifactError):
        evaluate(E.let_par((D,), (E.bv_lit(8, 1),), E.at(0, TermSort.bool())))
    with pytest.raises(ValueError):
        evaluate(E.at(0, B))
    with pytest.raises(ArtifactError):
        E.at(-1, B)


@given(st.integers(0, 255), st.integers(0, 255))
@settings(max_examples=80, derandomize=True)
def test_parallel_and_nested_semantics_and_z3(x, y):
    body = E.binary('bv_add', E.at(0, B), E.at(1, B))
    node = E.let_par((D, D), (E.bv_lit(8, x), E.bv_lit(8, y)), body)
    assert evaluate(node) == (x + y) % 256
    ctx = z3.Context()
    assert z3.simplify(expr_to_z3(node, {}, ctx)).as_long() == (x + y) % 256
    assert evaluate(loads(dumps(node))) == (x + y) % 256


@given(st.integers(0, 255), st.integers(0, 255))
@settings(max_examples=80, derandomize=True)
def test_substitution_evaluation_law(x, y):
    source = QFAbvContext((D,))
    rhs = E.binary('bv_add', E.at(0, B), E.bv_lit(8, y))
    update = QFAbvUpdate(source, source, (QFAbvExpr(source, decode_sort(B), rhs),))
    body = E.binary('bv_add', E.at(0, B), E.at(1, B))
    node = E.let_par((D,), (E.bv_lit(8, 4),), body)
    expression = QFAbvExpr(source, decode_sort(B), node)
    state = QFAbvValuation(source, (x,))
    assert eval_expr(expression.substitute(update), state) == eval_expr(expression, eval_update(update, state))


def test_z3_cache_separates_environments_and_contexts():
    node = E.at(0, B)
    memo = {}
    for ctx in (z3.Context(), z3.Context()):
        for number in (3, 9):
            env = [('x', z3.BitVecVal(number, 8, ctx))]
            result = expr_to_z3(node, env, ctx, memo=memo)
            assert result.ctx == ctx and result.as_long() == number
            assert expr_to_z3(node, env, ctx, memo=memo) is result


@pytest.mark.parametrize('rhs', [
    E.bool_lit(True), E.bv_lit(8, 17),
    E('const_array', TermSort.array(2, 8), (E.bv_lit(8, 23),)),
    E('rm_lit', TermSort.rounding_mode(), value='RNA'),
    E('bv_to_fp', TermSort.fp(8,24), (E.bv_lit(32,0x3f800000),)),
])
def test_parallel_bindings_preserve_every_sort(rhs):
    node = E.let_par((Declaration('value', rhs.sort),), (rhs,), E.at(0, rhs.sort))
    assert evaluate(node) == evaluate(rhs)
    assert evaluate(loads(dumps(node))) == evaluate(rhs)
    context = z3.Context()
    solver = z3.Solver(ctx=context)
    solver.add(expr_to_z3(node, {}, context) != expr_to_z3(rhs, {}, context))
    assert solver.check() == z3.unsat


def test_ordered_array_snapshot_binding():
    arr = TermSort.array(2,8)
    original = E('const_array', arr, (E.bv_lit(8,5),))
    read = E.select(E.at(0,arr), E.bv_lit(2,0))
    later = E('store',arr,(E.at(0,arr),E.bv_lit(2,0),E.bv_lit(8,9)))
    node = E.let_par((Declaration('memory',arr),),(original,),
        E.let_par((Declaration('old_read',B),Declaration('new_memory',arr)),(read,later),
            E.binary('bv_add',E.at(0,B),E.select(E.at(1,arr),E.bv_lit(2,0)))))
    assert evaluate(node) == 14


def test_binding_names_are_metadata_and_zero_extension_is_valid():
    for name in ('', '__ghot_memory_read_0__', 'arbitrary name', 'λ'):
        node = E.let_par((Declaration(name,B),),(E.bv_lit(8,23),),E.at(0,B))
        assert evaluate(loads(dumps(node))) == 23
    assert evaluate(E('zero_extend', B, (E.bv_lit(8,23),), amount=0)) == 23
