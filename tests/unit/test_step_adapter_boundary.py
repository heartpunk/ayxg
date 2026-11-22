"""The system-step boundary and cross-context adapter retain distinct roles."""

import pytest

from ayxg import (
    BoolSort, BVSort, Declaration, QFAbvAdapter, QFAbvAdapterSemantics,
    QFAbvContext, QFAbvExpr, QFAbvSTS, QFAbvStep, QFAbvUpdate,
    QFAbvValuation, TermSort, TypedExpr, eval_adapter, eval_step,
)


def expression(context, node):
    sort = BoolSort() if node.sort.kind == "bool" else BVSort(node.sort.width)
    return QFAbvExpr(context, sort, node)


def test_step_rejects_cross_context_updates_and_adapters_are_not_steps():
    bv = TermSort.bv(8)
    source = QFAbvContext((Declaration("x", bv),))
    target = QFAbvContext((Declaration("y", bv),))
    guard = expression(source, TypedExpr.bool_lit(True))
    update = QFAbvUpdate(source, target, (expression(source, TypedExpr.var("x", bv)),))

    with pytest.raises(ValueError, match="contexts must match"):
        QFAbvStep(guard, update)
    adapter = QFAbvAdapter(guard, update)
    assert eval_adapter(adapter, QFAbvValuation(source, (7,))) == QFAbvValuation(target, (7,))
    assert QFAbvAdapterSemantics().denotes(
        QFAbvValuation(source, (7,)), adapter, QFAbvValuation(target, (7,)))
    with pytest.raises(TypeError, match="QFAbvStep"):
        eval_step(adapter, QFAbvValuation(source, (7,)))
    with pytest.raises(ValueError, match="STS step"):
        QFAbvSTS(source, (QFAbvAdapter.identity(source),))


def test_adapter_composition_substitutes_updates_into_later_guards():
    bv = TermSort.bv(8)
    source = QFAbvContext((Declaration("x", bv),))
    middle = QFAbvContext((Declaration("y", bv),))
    target = QFAbvContext((Declaration("z", bv),))
    x, y = TypedExpr.var("x", bv), TypedExpr.var("y", bv)
    plus_one = lambda node: TypedExpr.binary("bv_add", node, TypedExpr.bv_lit(8, 1))
    first = QFAbvAdapter(expression(source, TypedExpr.bool_lit(True)),
        QFAbvUpdate(source, middle, (expression(source, plus_one(x)),)))
    second = QFAbvAdapter(expression(middle, TypedExpr.equal(y, TypedExpr.bv_lit(8, 8))),
        QFAbvUpdate(middle, target, (expression(middle, plus_one(y)),)))
    composed = first.compose(second)

    assert eval_adapter(composed, QFAbvValuation(source, (7,))) == QFAbvValuation(target, (9,))
    assert eval_adapter(composed, QFAbvValuation(source, (6,))) is None

    advance = QFAbvStep(expression(middle, TypedExpr.bool_lit(True)),
        QFAbvUpdate(middle, middle, (expression(middle, plus_one(y)),)))
    assert eval_adapter(first.compose_step(advance), QFAbvValuation(source, (7,))) == QFAbvValuation(middle, (9,))
    before = QFAbvStep.identity(source)
    assert eval_adapter(before.compose_adapter(first), QFAbvValuation(source, (7,))) == QFAbvValuation(middle, (8,))
    assert eval_step(before, QFAbvValuation(source, (7,))) == QFAbvValuation(source, (7,))
