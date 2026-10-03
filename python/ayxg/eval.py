"""Concrete evaluation of AYXG's admitted QF_ABV expression language.

Bit-vector operations follow SMT-LIB semantics, including division by zero.
Expressions remain structured data. Each shared node is evaluated once per
multi-root evaluation, without Python recursion. Updates read a single old
valuation, and disabled steps have no successor.
"""
from __future__ import annotations

from collections.abc import Mapping, Sequence
from typing import TypeVar, overload

from .expr import ArtifactError, TypedExpr
from .qfabv import (
    ArraySort, BoolSort, BVSort, QFAbvArrayValue, QFAbvExpr, QFAbvStep,
    QFAbvUpdate, QFAbvValuation, Sort, Value,
)

C = TypeVar("C")
D = TypeVar("D")


def _integer(value: Value) -> int:
    if type(value) is not int:
        raise ArtifactError("expected bit-vector value")
    return value


def _boolean(value: Value) -> bool:
    if type(value) is not bool:
        raise ArtifactError("expected Boolean value")
    return value


def _array(value: Value) -> QFAbvArrayValue:
    if not isinstance(value, QFAbvArrayValue):
        raise ArtifactError("expected array value")
    return value


def _signed(value: int, width: int) -> int:
    return value - (1 << width) if value & (1 << (width - 1)) else value


def _apply(node: TypedExpr, args: tuple[Value, ...], variables: Mapping[str, Value]) -> Value:
    op = node.op
    if op == "var":
        assert node.name is not None
        return variables[node.name]
    if op in {"bool_lit", "bv_lit"}:
        assert node.value is not None
        return node.value
    if op == "const_array":
        iw, vw = node.sort.require_array_widths()
        return QFAbvArrayValue(ArraySort(iw, vw), _integer(args[0]))
    if op == "bool_not":
        return not _boolean(args[0])
    if op == "bool_and":
        return _boolean(args[0]) and _boolean(args[1])
    if op == "bool_or":
        return _boolean(args[0]) or _boolean(args[1])
    if op == "ite":
        return args[1] if _boolean(args[0]) else args[2]
    if op == "eq":
        return _equal_values(args[0], args[1])
    if op == "select":
        array = _array(args[0])
        return dict(array.entries).get(_integer(args[1]), array.default)
    if op == "store":
        array = _array(args[0])
        index, value = _integer(args[1]), _integer(args[2])
        entries = dict(array.entries)
        if value == array.default:
            entries.pop(index, None)
        else:
            entries[index] = value
        return QFAbvArrayValue(array.sort, array.default, tuple(sorted(entries.items())))

    # From here on, inputs are bitvectors. The node validator establishes sorts.
    left = _integer(args[0])
    width = node.args[0].sort.require_bv_width()
    mask = (1 << width) - 1
    if op == "bv_not":
        return left ^ mask
    if op == "zero_extend":
        return left
    if op == "sign_extend":
        return _signed(left, width) & ((1 << node.sort.require_bv_width()) - 1)
    if op == "extract":
        assert node.lo is not None
        return (left >> node.lo) & ((1 << node.sort.require_bv_width()) - 1)
    right = _integer(args[1])
    if op == "concat":
        return (left << node.args[1].sort.require_bv_width()) | right
    if op == "bv_ult":
        return left < right
    if op == "bv_ule":
        return left <= right
    if op == "bv_slt":
        return _signed(left, width) < _signed(right, width)
    if op == "bv_sle":
        return _signed(left, width) <= _signed(right, width)
    if op == "bv_add":
        return (left + right) & mask
    if op == "bv_sub":
        return (left - right) & mask
    if op == "bv_mul":
        return (left * right) & mask
    if op == "bv_udiv":
        return mask if right == 0 else left // right
    if op == "bv_urem":
        return left if right == 0 else left % right
    if op == "bv_and":
        return left & right
    if op == "bv_or":
        return left | right
    if op == "bv_xor":
        return left ^ right
    # Saturate oversized shifts before shifting: do not allocate huge integers.
    if op == "bv_shl":
        return 0 if right >= width else (left << right) & mask
    if op == "bv_lshr":
        return 0 if right >= width else left >> right
    if op == "bv_ashr":
        signed = _signed(left, width)
        if right >= width:
            return mask if signed < 0 else 0
        return (signed >> right) & mask
    raise ArtifactError(f"unsupported expression operator {op!r}")


def _eval_nodes(roots: Sequence[TypedExpr], variables: Mapping[str, Value]) -> tuple[Value, ...]:
    memo: dict[int, Value] = {}
    for root in roots:
        stack = [(root, False)]
        while stack:
            node, expanded = stack.pop()
            key = id(node)
            if key in memo:
                continue
            if expanded:
                memo[key] = _apply(node, tuple(memo[id(arg)] for arg in node.args), variables)
            else:
                stack.append((node, True))
                stack.extend((arg, False) for arg in reversed(node.args) if id(arg) not in memo)
    return tuple(memo[id(root)] for root in roots)


def eval_exprs(expressions: Sequence[QFAbvExpr[C, Sort]],
               state: QFAbvValuation[C]) -> tuple[Value, ...]:
    """Evaluate several roots together, retaining sharing across all of them."""
    if any(expression.context != state.context for expression in expressions):
        raise ValueError("expression and valuation contexts disagree")
    variables = {d.name: value for d, value in zip(state.context.declarations, state.values)}
    return _eval_nodes(tuple(expression.node for expression in expressions), variables)


@overload
def eval_expr(expression: QFAbvExpr[C, BoolSort], state: QFAbvValuation[C]) -> bool: ...
@overload
def eval_expr(expression: QFAbvExpr[C, BVSort], state: QFAbvValuation[C]) -> int: ...
@overload
def eval_expr(expression: QFAbvExpr[C, ArraySort], state: QFAbvValuation[C]) -> QFAbvArrayValue: ...
@overload
def eval_expr(expression: QFAbvExpr[C, Sort], state: QFAbvValuation[C]) -> Value: ...
def eval_expr(expression: QFAbvExpr[C, Sort], state: QFAbvValuation[C]) -> Value:
    return eval_exprs((expression,), state)[0]


def eval_update(update: QFAbvUpdate[C, D], state: QFAbvValuation[C]) -> QFAbvValuation[D]:
    """All RHSs see the same old state, even when output names overlap."""
    if update.source != state.context:
        raise ValueError("update and valuation contexts disagree")
    return QFAbvValuation(update.target, eval_exprs(update.rhs, state))


def eval_step(step: QFAbvStep[C, D], state: QFAbvValuation[C]) -> QFAbvValuation[D] | None:
    """Return the guarded successor, or None when the step is disabled."""
    if not eval_expr(step.guard, state):
        return None
    return eval_update(step.update, state)


def _equal_values(left: Value, right: Value) -> bool:
    if isinstance(left, QFAbvArrayValue) and isinstance(right, QFAbvArrayValue):
        if left.sort != right.sort:
            return False
        lhs, rhs = dict(left.entries), dict(right.entries)
        keys = lhs.keys() | rhs.keys()
        if left.default != right.default and len(keys) < (1 << left.sort.index_width):
            return False
        return all(lhs.get(key, left.default) == rhs.get(key, right.default) for key in keys)
    return type(left) is type(right) and left == right


def equal_valuations(left: QFAbvValuation[C], right: QFAbvValuation[C]) -> bool:
    """Array-valued states are compared extensionally, not by their encoding."""
    return left.context == right.context and all(
        _equal_values(a, b) for a, b in zip(left.values, right.values))


class QFAbvSemantics:
    """Interpreter for QFAbvStep data, conforming to RelationSemantics."""
    def denotes(self, source: QFAbvValuation[C], step: QFAbvStep[C, D],
                target: QFAbvValuation[D], /) -> bool:
        if source.context != step.update.source or target.context != step.update.target:
            return False
        successor = eval_step(step, source)
        return successor is not None and equal_valuations(successor, target)
