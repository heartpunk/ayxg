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
from .fp import FPInterpretation
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


def _apply(node: TypedExpr, args: tuple[Value, ...], variables: Mapping[str, Value], fp_interpretation: FPInterpretation | None = None) -> Value:
    op = node.op
    if op == "var":
        assert node.name is not None
        return variables[node.name]
    if op in {"bool_lit", "bv_lit"}:
        assert node.value is not None
        return node.value
    if op == "rm_lit" or op.startswith("fp_") or op in {"bv_to_fp", "sbv_to_fp", "ubv_to_fp"}:
        from .fp_z3 import evaluate_fp_node
        return evaluate_fp_node(node, args, fp_interpretation)
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


def _eval_nodes(roots: Sequence[TypedExpr], variables: Mapping[str, Value], fp_interpretation: FPInterpretation | None = None) -> tuple[Value, ...]:
    memo: dict[int, Value] = {}
    for root in roots:
        stack = [(root, False)]
        while stack:
            node, expanded = stack.pop()
            key = id(node)
            if key in memo:
                continue
            if node.op in {"ite", "bool_and", "bool_or"}:
                condition = node.args[0]
                if id(condition) not in memo:
                    stack.extend(((node, False), (condition, False)))
                    continue
                test = _boolean(memo[id(condition)])
                if node.op == "bool_and" and not test or node.op == "bool_or" and test:
                    memo[key] = test
                    continue
                chosen = node.args[1 if test or node.op != "ite" else 2]
                if id(chosen) not in memo:
                    stack.extend(((node, False), (chosen, False)))
                    continue
                memo[key] = memo[id(chosen)]
                continue
            if expanded:
                memo[key] = _apply(node, tuple(memo[id(arg)] for arg in node.args), variables, fp_interpretation)
            else:
                stack.append((node, True))
                stack.extend((arg, False) for arg in reversed(node.args) if id(arg) not in memo)
    return tuple(memo[id(root)] for root in roots)


def eval_exprs(expressions: Sequence[QFAbvExpr[C, Sort]],
               state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> tuple[Value, ...]:
    """Evaluate several roots together, retaining sharing across all of them."""
    if any(expression.context != state.context for expression in expressions):
        raise ValueError("expression and valuation contexts disagree")
    variables = {d.name: value for d, value in zip(state.context.declarations, state.values)}
    return _eval_nodes(tuple(expression.node for expression in expressions), variables, fp_interpretation)


@overload
def eval_expr(expression: QFAbvExpr[C, BoolSort], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> bool: ...
@overload
def eval_expr(expression: QFAbvExpr[C, BVSort], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> int: ...
@overload
def eval_expr(expression: QFAbvExpr[C, ArraySort], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> QFAbvArrayValue: ...
@overload
def eval_expr(expression: QFAbvExpr[C, Sort], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> Value: ...
def eval_expr(expression: QFAbvExpr[C, Sort], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> Value:
    return eval_exprs((expression,), state, fp_interpretation)[0]


def eval_update(update: QFAbvUpdate[C, D], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> QFAbvValuation[D]:
    """All RHSs see the same old state, even when output names overlap."""
    if update.source != state.context:
        raise ValueError("update and valuation contexts disagree")
    return QFAbvValuation(update.target, eval_exprs(update.rhs, state, fp_interpretation))


def eval_step(step: QFAbvStep[C, D], state: QFAbvValuation[C], fp_interpretation: FPInterpretation | None = None) -> QFAbvValuation[D] | None:
    """Return the guarded successor, or None when the step is disabled."""
    if not eval_expr(step.guard, state, fp_interpretation):
        return None
    return eval_update(step.update, state, fp_interpretation)


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
    def __init__(self, fp_interpretation: FPInterpretation | None = None):
        self.fp_interpretation = fp_interpretation

    def denotes(self, source: QFAbvValuation[C], step: QFAbvStep[C, D],
                target: QFAbvValuation[D], /) -> bool:
        if source.context != step.update.source or target.context != step.update.target:
            return False
        successor = eval_step(step, source, self.fp_interpretation)
        return successor is not None and equal_valuations(successor, target)
