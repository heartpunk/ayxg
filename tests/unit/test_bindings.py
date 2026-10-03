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
