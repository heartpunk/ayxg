"""Hypothesis checks for the simple algebraic laws of Python QF_ABV data."""
from hypothesis import given, strategies as st

from ayxg import (
    BoolSort, Declaration, QFAbvContext, QFAbvExpr, QFAbvStep, QFAbvUpdate,
    QFAbvValuation, TermSort, TypedExpr, equal_valuations, eval_expr,
    eval_step, eval_update,
)
from ayxg.qfabv import BVSort


@st.composite
def states_and_updates(draw):
    width = draw(st.integers(min_value=1, max_value=16))
    mask = (1 << width) - 1
    x, y = Declaration("x", TermSort.bv(width)), Declaration("y", TermSort.bv(width))
    context = QFAbvContext((x, y))
    state = QFAbvValuation(context, (draw(st.integers(0, mask)), draw(st.integers(0, mask))))
    def update(target, names):
        nodes = []
        for name in names:
            source = draw(st.sampled_from(["x", "y", "literal"]))
            if source == "literal":
                node = TypedExpr.bv_lit(width, draw(st.integers(0, mask)))
            else:
                node = TypedExpr.var(source, TermSort.bv(width))
            nodes.append(QFAbvExpr(context, BVSort(width), node))
        return QFAbvUpdate(context, target, tuple(nodes))
    first = update(context, ("x", "y"))
    second = update(context, ("x", "y"))
    third = update(context, ("x", "y"))
    return state, first, second, third


@given(states_and_updates())
def test_update_identity_and_composition_match_execution(case):
    state, first, second, _ = case
    identity = QFAbvUpdate.identity(state.context)
    assert equal_valuations(eval_update(identity, state), state)
    assert equal_valuations(eval_update(first.compose(identity), state), eval_update(first, state))
    assert equal_valuations(eval_update(identity.compose(first), state), eval_update(first, state))
    composed = eval_update(first.compose(second), state)
    sequential = eval_update(second, eval_update(first, state))
    assert equal_valuations(composed, sequential)


@given(states_and_updates())
def test_three_update_composition_is_associative_semantically(case):
    state, a, b, c = case
    left = eval_update(a.compose(b).compose(c), state)
    right = eval_update(a.compose(b.compose(c)), state)
    assert equal_valuations(left, right)


@given(st.integers(0, 255), st.integers(0, 255))
def test_simultaneous_swap_reads_the_old_state(x, y):
    ctx = QFAbvContext((Declaration("x", TermSort.bv(8)), Declaration("y", TermSort.bv(8))))
    before = QFAbvValuation(ctx, (x, y))
    swap = QFAbvUpdate(ctx, ctx, (
        QFAbvExpr(ctx, BVSort(8), TypedExpr.var("y", TermSort.bv(8))),
        QFAbvExpr(ctx, BVSort(8), TypedExpr.var("x", TermSort.bv(8))),
    ))
    assert eval_update(swap, before).values == (y, x)


@given(states_and_updates(), st.booleans(), st.booleans())
def test_step_composition_agrees_with_sequential_guarded_execution(case, first_enabled, second_enabled):
    state, first_update, second_update, _ = case
    def step(update, enabled):
        guard = QFAbvExpr(state.context, BoolSort(), TypedExpr.bool_lit(enabled))
        return QFAbvStep(guard, update)
    first, second = step(first_update, first_enabled), step(second_update, second_enabled)
    sequential = eval_step(second, eval_step(first, state)) if first_enabled else None
    composed = eval_step(first.compose(second), state)
    if sequential is None:
        assert composed is None
    else:
        assert composed is not None and equal_valuations(composed, sequential)


@given(st.integers(0, 255), st.integers(0, 255))
def test_substitution_is_simultaneous_and_preserves_evaluation(x, y):
    from ayxg.substitution import substitute_exprs
    width = TermSort.bv(8)
    ctx = QFAbvContext((Declaration("x", width), Declaration("y", width)))
    state = QFAbvValuation(ctx, (x, y))
    root = TypedExpr.binary("bv_sub", TypedExpr.var("x", width), TypedExpr.var("y", width))
    swapped = substitute_exprs((root, root), {
        "x": TypedExpr.var("y", width), "y": TypedExpr.var("x", width)})
    assert swapped[0] is swapped[1]
    result = eval_expr(QFAbvExpr(ctx, BVSort(8), swapped[0]), state)
    assert result == (y - x) % 256


@given(states_and_updates())
def test_guarded_step_composition_is_associative(case):
    state, a, b, c = case
    def always(update):
        return QFAbvStep(QFAbvExpr(state.context, BoolSort(), TypedExpr.bool_lit(True)), update)
    left = always(a).compose(always(b)).compose(always(c))
    right = always(a).compose(always(b).compose(always(c)))
    left_result, right_result = eval_step(left, state), eval_step(right, state)
    assert left_result is not None and right_result is not None
    assert equal_valuations(left_result, right_result)
