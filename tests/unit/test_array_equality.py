"""Extensional array equality, including differing finite-support encodings."""
from hypothesis import given, strategies as st
from ayxg.expr import TypedExpr, TermSort
from ayxg.qfabv import ArraySort, QFAbvArrayValue
from ayxg.eval import _eval_nodes


def test_distinct_encodings_same_total_array():
    sort = ArraySort(1, 8)
    a = QFAbvArrayValue(sort, 0, ((1, 1),))
    b = QFAbvArrayValue(sort, 1, ((0, 0),))
    assert a != b
    expr = TypedExpr.equal(TypedExpr.var("a", sort.encode()), TypedExpr.var("b", sort.encode()))
    assert _eval_nodes((expr,), {"a": a, "b": b}) == (True,)
    assert TypedExpr.from_data(expr.to_data()) == expr


@given(st.lists(st.integers(0, 7), min_size=4, max_size=4),
       st.lists(st.integers(0, 7), min_size=4, max_size=4),
       st.integers(0, 7), st.integers(0, 7))
def test_extensional_equality(left, right, ld, rd):
    sort = ArraySort(2, 3)
    a = QFAbvArrayValue(sort, ld, tuple((i,v) for i,v in enumerate(left) if v != ld))
    b = QFAbvArrayValue(sort, rd, tuple((i,v) for i,v in enumerate(right) if v != rd))
    expr = TypedExpr.equal(TypedExpr.var("a", sort.encode()), TypedExpr.var("b", sort.encode()))
    assert _eval_nodes((expr,), {"a": a, "b": b}) == (left == right,)


def test_large_sparse_array_equality():
    sort = ArraySort(64, 8)
    a = QFAbvArrayValue(sort, 0, ((123, 9),))
    b = QFAbvArrayValue(sort, 0, ((124, 9),))
    expr = TypedExpr.equal(TypedExpr.var("a", sort.encode()), TypedExpr.var("b", sort.encode()))
    assert _eval_nodes((expr,), {"a": a, "b": a}) == (True,)
    assert _eval_nodes((expr,), {"a": a, "b": b}) == (False,)
