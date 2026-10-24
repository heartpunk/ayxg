"""WRUH's QF_ABV expression syntax, imported by ast-grep declaration spans.

This syntax includes positional variables and parallel bindings, with positive-width, canonical literals from
Ayxg.QfAbv.Expr. Context membership is provided by ayxg.qfabv.QFAbvExpr.
"""
from __future__ import annotations

import re
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import Any, cast


class ArtifactError(ValueError):
    """An expression violates its structural typing contract."""


class UnsupportedTheoryError(ArtifactError):
    """An input uses a theory or operator outside the admitted QF_ABV surface."""

_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._:-]*\Z")

def _nonnegative(value: Any, field: str) -> int:
    if type(value) is not int or value < 0:
        raise ArtifactError(f"{field} must be a nonnegative integer")
    return value

def _identifier(value: Any, field: str) -> str:
    if not isinstance(value, str):
        raise ArtifactError(f"{field} must be a string")
    return value

def _text(value: Any, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise ArtifactError(f"{field} must be a nonempty string")
    return value

def _object(value: Any, field: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        raise ArtifactError(f"{field} must be an object")
    return cast(Mapping[str, Any], value)

def _array(value: Any, field: str) -> list[Any]:
    if not isinstance(value, list):
        raise ArtifactError(f"{field} must be an array")
    return cast(list[Any], value)

def _fields(value: Mapping[str, Any], expected: set[str], field: str) -> None:
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise ArtifactError(
            f"{field} fields differ: missing={missing}, extra={extra}"
        )

@dataclass(frozen=True, order=True)
class TermSort:
    """A strict transport-level QF_ABV sort."""

    kind: str
    width: int | None = None
    index_width: int | None = None
    value_width: int | None = None
    exponent_bits: int | None = None
    significand_bits: int | None = None

    def __post_init__(self) -> None:
        if self.kind not in {"fp"} and (self.exponent_bits is not None or self.significand_bits is not None):
            raise ArtifactError("only FP sorts carry exponent/significand widths")
        if self.kind == "rm":
            if any(v is not None for v in (self.width, self.index_width, self.value_width)):
                raise ArtifactError("rounding-mode sort must not carry widths")
        elif self.kind == "fp":
            if (type(self.exponent_bits) is not int or self.exponent_bits < 2
                    or type(self.significand_bits) is not int or self.significand_bits < 2
                    or any(v is not None for v in (self.width, self.index_width, self.value_width))):
                raise ArtifactError("FP sort requires exponent/significand widths >= 2")
        elif self.kind == "bool":
            if (
                self.width is not None
                or self.index_width is not None
                or self.value_width is not None
            ):
                raise ArtifactError("bool sort must not carry widths")
        elif self.kind == "bv":
            if (
                type(self.width) is not int
                or self.width <= 0
                or self.index_width is not None
                or self.value_width is not None
            ):
                raise ArtifactError("bv sort requires exactly one positive width")
        elif self.kind == "array":
            if (
                self.width is not None
                or type(self.index_width) is not int
                or self.index_width <= 0
                or type(self.value_width) is not int
                or self.value_width <= 0
            ):
                raise ArtifactError(
                    "array sort requires positive index and value widths"
                )
        else:
            raise ArtifactError(f"unknown term sort: {self.kind!r}")

    @classmethod
    def bool(cls) -> TermSort:
        return cls("bool")

    @classmethod
    def bv(cls, width: int) -> TermSort:
        return cls("bv", width=width)

    @classmethod
    def array(cls, index_width: int, value_width: int) -> TermSort:
        return cls(
            "array",
            index_width=index_width,
            value_width=value_width,
        )

    @classmethod
    def fp(cls, exponent_bits: int, significand_bits: int) -> TermSort:
        return cls("fp", exponent_bits=exponent_bits, significand_bits=significand_bits)

    @classmethod
    def rounding_mode(cls) -> TermSort:
        return cls("rm")

    def require_fp_widths(self) -> tuple[int, int]:
        if self.kind != "fp":
            raise ArtifactError("expected floating-point sort")
        assert self.exponent_bits is not None and self.significand_bits is not None
        return self.exponent_bits, self.significand_bits

    def require_bv_width(self) -> int:
        if self.kind != "bv" or self.width is None:
            raise ArtifactError("expected bit-vector sort")
        return self.width

    def require_array_widths(self) -> tuple[int, int]:
        if self.kind != "array" or self.index_width is None or self.value_width is None:
            raise ArtifactError("expected array sort")
        return self.index_width, self.value_width

    def to_data(self) -> dict[str, Any]:
        if self.kind == "rm":
            return {"kind": "rm"}
        if self.kind == "fp":
            return {"kind": "fp", "exponent_bits": self.exponent_bits, "significand_bits": self.significand_bits}
        if self.kind == "bool":
            return {"kind": "bool"}
        if self.kind == "bv":
            return {"kind": "bv", "width": self.width}
        return {
            "kind": "array",
            "index_width": self.index_width,
            "value_width": self.value_width,
        }

    @classmethod
    def from_data(cls, value: Any, field: str = "sort") -> TermSort:
        obj = _object(value, field)
        kind = obj.get("kind")
        if kind == "rm":
            _fields(obj, {"kind"}, field)
            return cls.rounding_mode()
        if kind == "fp":
            _fields(obj, {"kind", "exponent_bits", "significand_bits"}, field)
            return cls.fp(_nonnegative(obj["exponent_bits"], field), _nonnegative(obj["significand_bits"], field))
        if kind == "bool":
            _fields(obj, {"kind"}, field)
            return cls.bool()
        if kind == "bv":
            _fields(obj, {"kind", "width"}, field)
            return cls.bv(_nonnegative(obj["width"], f"{field}.width"))
        if kind == "array":
            _fields(
                obj,
                {"kind", "index_width", "value_width"},
                field,
            )
            return cls.array(
                _nonnegative(
                    obj["index_width"], f"{field}.index_width"
                ),
                _nonnegative(
                    obj["value_width"], f"{field}.value_width"
                ),
            )
        raise ArtifactError(f"{field} has unknown sort kind: {kind!r}")

BOOL = TermSort.bool()

@dataclass(frozen=True, order=True)
class Declaration:
    name: str
    sort: TermSort

    def __post_init__(self) -> None:
        _identifier(self.name, "declaration.name")

    def to_data(self) -> dict[str, Any]:
        return {"name": self.name, "sort": self.sort.to_data()}

    @classmethod
    def from_data(
        cls,
        value: Any,
        field: str = "declaration",
    ) -> Declaration:
        obj = _object(value, field)
        _fields(obj, {"name", "sort"}, field)
        return cls(
            _identifier(obj["name"], f"{field}.name"),
            TermSort.from_data(obj["sort"], f"{field}.sort"),
        )

_UNARY_OPS = {"bool_not", "bv_not"}
_BINARY_BOOL_OPS = {"bool_and", "bool_or"}
_BINARY_BV_OPS = {
    "bv_add",
    "bv_sub",
    "bv_mul",
    "bv_udiv",
    "bv_sdiv",
    "bv_urem",
    "bv_and",
    "bv_or",
    "bv_xor",
    "bv_shl",
    "bv_lshr",
    "bv_ashr",
}
_BV_CMP_OPS = {"bv_ult", "bv_ule", "bv_slt", "bv_sle"}
_EXTEND_OPS = {"zero_extend", "sign_extend"}


@dataclass(frozen=True)
class TypedExpr:
    """A closed, sort-checked transport node for the admitted QF_ABV subset."""

    op: str
    sort: TermSort
    args: tuple[TypedExpr, ...] = ()
    name: str | None = None
    value: bool | int | str | None = None
    amount: int | None = None
    hi: int | None = None
    lo: int | None = None
    index: int | None = None
    bindings: tuple[Declaration, ...] | None = None

    def __post_init__(self) -> None:
        expected_metadata: set[str]
        if self.op == "var":
            if self.index is None:
                expected_metadata = {"name"}
                _identifier(self.name, "expression.name")
            else:
                expected_metadata = {"index"}
                _nonnegative(self.index, "expression.index")
            self._require_arity(0)
        elif self.op == "let_par":
            expected_metadata = {"bindings"}
            if not isinstance(self.bindings, tuple) or any(not isinstance(d, Declaration) for d in self.bindings):
                raise ArtifactError("let_par requires a tuple of declarations")
            self._require_arity(len(self.bindings) + 1)
            if tuple(a.sort for a in self.args[:-1]) != tuple(d.sort for d in self.bindings) or self.args[-1].sort != self.sort:
                raise ArtifactError("let_par binding or body sort disagrees")
        elif self.op == "bool_lit":
            expected_metadata = {"value"}
            if self.sort != BOOL or type(self.value) is not bool:
                raise ArtifactError("bool_lit requires a Bool sort and value")
            self._require_arity(0)
        elif self.op == "bv_lit":
            expected_metadata = {"value"}
            if (
                self.sort.kind != "bv"
                or type(self.value) is not int
                or self.value < 0
                or self.value >= (1 << self.sort.require_bv_width())
            ):
                raise ArtifactError(
                    "bv_lit value must be canonical for its positive width"
                )
            self._require_arity(0)
        elif self.op == "rm_lit":
            expected_metadata = {"value"}
            self._require_arity(0)
            if self.sort != TermSort.rounding_mode() or self.value not in {"RNE", "RNA", "RTP", "RTN", "RTZ"}:
                raise ArtifactError("invalid rounding-mode literal")
        elif self.op.startswith("fp_") or self.op in {"bv_to_fp", "sbv_to_fp", "ubv_to_fp"}:
            expected_metadata = set()
            from .fp import check_fp_node
            check_fp_node(self)
        elif self.op == "const_array":
            expected_metadata = set()
            self._require_arity(1)
            if (
                self.sort.kind != "array"
                or self.args[0].sort != TermSort.bv(self.sort.require_array_widths()[1])
            ):
                raise ArtifactError("const_array value sort disagrees")
        elif self.op in _UNARY_OPS:
            expected_metadata = set()
            self._require_arity(1)
            if self.op == "bool_not":
                self._require_sorts(BOOL, BOOL)
            elif self.sort.kind != "bv" or self.args[0].sort != self.sort:
                raise ArtifactError("bv_not operand sort disagrees")
        elif self.op in _BINARY_BOOL_OPS:
            expected_metadata = set()
            self._require_arity(2)
            self._require_sorts(BOOL, BOOL, BOOL)
        elif self.op in _BINARY_BV_OPS:
            expected_metadata = set()
            self._require_arity(2)
            if (
                self.sort.kind != "bv"
                or self.args[0].sort != self.sort
                or self.args[1].sort != self.sort
            ):
                raise ArtifactError(f"{self.op} operand sorts disagree")
        elif self.op == "ite":
            expected_metadata = set()
            self._require_arity(3)
            if (
                self.args[0].sort != BOOL
                or self.args[1].sort != self.sort
                or self.args[2].sort != self.sort
            ):
                raise ArtifactError("ite branch sorts disagree")
        elif self.op in _EXTEND_OPS:
            expected_metadata = {"amount"}
            self._require_arity(1)
            if (
                type(self.amount) is not int
                or self.amount < 0
                or self.args[0].sort.kind != "bv"
                or self.sort
                != TermSort.bv(self.args[0].sort.require_bv_width() + self.amount)
            ):
                raise ArtifactError(f"{self.op} widths disagree")
        elif self.op == "extract":
            expected_metadata = {"hi", "lo"}
            self._require_arity(1)
            if (
                type(self.hi) is not int
                or type(self.lo) is not int
                or self.args[0].sort.kind != "bv"
                or not 0 <= self.lo <= self.hi < self.args[0].sort.require_bv_width()
                or self.sort != TermSort.bv(self.hi - self.lo + 1)
            ):
                raise ArtifactError("extract bounds or result width disagree")
        elif self.op == "concat":
            expected_metadata = set()
            self._require_arity(2)
            if (
                self.args[0].sort.kind != "bv"
                or self.args[1].sort.kind != "bv"
                or self.sort
                != TermSort.bv(
                    self.args[0].sort.require_bv_width() + self.args[1].sort.require_bv_width()
                )
            ):
                raise ArtifactError("concat operand or result sorts disagree")
        elif self.op == "select":
            expected_metadata = set()
            self._require_arity(2)
            array_sort = self.args[0].sort
            if (
                array_sort.kind != "array"
                or self.args[1].sort != TermSort.bv(array_sort.require_array_widths()[0])
                or self.sort != TermSort.bv(array_sort.require_array_widths()[1])
            ):
                raise ArtifactError("select operand or result sorts disagree")
        elif self.op == "store":
            expected_metadata = set()
            self._require_arity(3)
            if (
                self.sort.kind != "array"
                or self.args[0].sort != self.sort
                or self.args[1].sort != TermSort.bv(self.sort.require_array_widths()[0])
                or self.args[2].sort != TermSort.bv(self.sort.require_array_widths()[1])
            ):
                raise ArtifactError("store operand or result sorts disagree")
        elif self.op in _BV_CMP_OPS:
            expected_metadata = set()
            self._require_arity(2)
            if (
                self.sort != BOOL
                or self.args[0].sort.kind != "bv"
                or self.args[1].sort != self.args[0].sort
            ):
                raise ArtifactError(f"{self.op} operand sorts disagree")
        elif self.op == "eq":
            expected_metadata = set()
            self._require_arity(2)
            if (
                self.sort != BOOL
                or self.args[0].sort != self.args[1].sort
            ):
                raise ArtifactError("eq requires equal operand sorts")
        else:
            raise ArtifactError(f"unknown typed expression operator: {self.op!r}")

        metadata = {
            key
            for key, item in (
                ("name", self.name),
                ("value", self.value),
                ("amount", self.amount),
                ("hi", self.hi),
                ("lo", self.lo),
                ("index", self.index),
                ("bindings", self.bindings),
            )
            if item is not None
        }
        if metadata != expected_metadata:
            raise ArtifactError(
                f"{self.op} metadata differs: expected={sorted(expected_metadata)}, "
                f"actual={sorted(metadata)}"
            )

    def _require_arity(self, count: int) -> None:
        if len(self.args) != count:
            raise ArtifactError(f"{self.op} requires {count} operands")

    def _require_sorts(self, result: TermSort, *args: TermSort) -> None:
        if self.sort != result or tuple(item.sort for item in self.args) != args:
            raise ArtifactError(f"{self.op} operand or result sorts disagree")

    @classmethod
    def var(cls, name: str, sort: TermSort) -> TypedExpr:
        return cls("var", sort, name=name)

    @classmethod
    def at(cls, index: int, sort: TermSort) -> TypedExpr:
        """Typed reference to a context slot; zero is the context head."""
        return cls("var", sort, index=index)

    @classmethod
    def let_par(cls, bindings: tuple[Declaration, ...], rhs: tuple[TypedExpr, ...], body: TypedExpr) -> TypedExpr:
        """All RHSs see the old context; body sees bindings prepended in order."""
        return cls("let_par", body.sort, (*rhs, body), bindings=bindings)

    @classmethod
    def bool_lit(cls, value: bool) -> TypedExpr:
        return cls("bool_lit", BOOL, value=value)

    @classmethod
    def bv_lit(cls, width: int, value: int) -> TypedExpr:
        return cls("bv_lit", TermSort.bv(width), value=value)

    @classmethod
    def unary(cls, op: str, arg: TypedExpr) -> TypedExpr:
        sort = BOOL if op == "bool_not" else arg.sort
        return cls(op, sort, (arg,))

    @classmethod
    def binary(cls, op: str, lhs: TypedExpr, rhs: TypedExpr) -> TypedExpr:
        sort = BOOL if op in _BINARY_BOOL_OPS | _BV_CMP_OPS | {"eq"} else lhs.sort
        return cls(op, sort, (lhs, rhs))

    @classmethod
    def negate(cls, expression: TypedExpr) -> TypedExpr:
        return cls("bool_not", BOOL, (expression,))

    @classmethod
    def conjoin(cls, *expressions: TypedExpr) -> TypedExpr:
        result = expressions[0] if expressions else cls.bool_lit(True)
        for expression in expressions[1:]:
            result = cls("bool_and", BOOL, (result, expression))
        return result

    @classmethod
    def disjoin(cls, *expressions: TypedExpr) -> TypedExpr:
        result = expressions[0] if expressions else cls.bool_lit(False)
        for expression in expressions[1:]:
            result = cls("bool_or", BOOL, (result, expression))
        return result

    @classmethod
    def equal(cls, left: TypedExpr, right: TypedExpr) -> TypedExpr:
        return cls("eq", BOOL, (left, right))

    @classmethod
    def not_equal(cls, left: TypedExpr, right: TypedExpr) -> TypedExpr:
        return cls.negate(cls.equal(left, right))

    @classmethod
    def select(cls, array: TypedExpr, index: TypedExpr) -> TypedExpr:
        return cls(
            "select",
            TermSort.bv(array.sort.require_array_widths()[1]),
            (array, index),
        )

    @classmethod
    def extract(cls, expression: TypedExpr, high: int, low: int) -> TypedExpr:
        return cls(
            "extract",
            TermSort.bv(high - low + 1),
            (expression,),
            hi=high,
            lo=low,
        )

    @classmethod
    def sign_extend(cls, expression: TypedExpr, amount: int) -> TypedExpr:
        return cls(
            "sign_extend",
            TermSort.bv(expression.sort.require_bv_width() + amount),
            (expression,),
            amount=amount,
        )

    @classmethod
    def concat_all(cls, expressions: Iterable[TypedExpr]) -> TypedExpr:
        items = iter(expressions)
        result = next(items)
        for expression in items:
            result = cls(
                "concat",
                TermSort.bv(result.sort.require_bv_width() + expression.sort.require_bv_width()),
                (result, expression),
            )
        return result

    @classmethod
    def ite(
        cls,
        condition: TypedExpr,
        then_value: TypedExpr,
        else_value: TypedExpr,
    ) -> TypedExpr:
        return cls("ite", then_value.sort, (condition, then_value, else_value))

    def variable_sorts(self) -> dict[str, TermSort]:
        return variable_sorts((self,))

    def to_data(self) -> dict[str, Any]:
        # Preserve sharing while exposing expression data to the artifact codec.
        memo: dict[int, dict[str, Any]] = {}
        stack = [(self, False)]
        while stack:
            node, ready = stack.pop()
            if id(node) in memo:
                continue
            if not ready:
                stack.append((node, True))
                stack.extend((arg, False) for arg in reversed(node.args))
                continue
            result: dict[str, Any] = {"op": node.op, "sort": node.sort.to_data()}
            if node.args:
                result["args"] = [memo[id(arg)] for arg in node.args]
            for key in ("name", "value", "amount", "hi", "lo", "index"):
                value = getattr(node, key)
                if value is not None:
                    result[key] = value
            if node.bindings is not None:
                result["bindings"] = [d.to_data() for d in node.bindings]
            memo[id(node)] = result
        return memo[id(self)]

    @classmethod
    def from_data(
        cls,
        value: Any,
        field: str = "expression",
    ) -> TypedExpr:
        if isinstance(value, cls):
            return value
        obj = _object(value, field)
        op = _text(obj.get("op"), f"{field}.op")
        expected = {"op", "sort"}
        if op in {"var"}:
            expected.add("index" if "index" in obj else "name")
        elif op == "let_par":
            expected |= {"args", "bindings"}
        elif op in {"bool_lit", "bv_lit", "rm_lit"}:
            expected.add("value")
        elif op in _EXTEND_OPS:
            expected |= {"args", "amount"}
        elif op == "extract":
            expected |= {"args", "hi", "lo"}
        elif op not in {"var", "bool_lit", "bv_lit", "rm_lit"}:
            expected.add("args")
        _fields(obj, expected, field)
        args = tuple(
            cls.from_data(arg, f"{field}.args[]")
            for arg in _array(obj["args"], f"{field}.args")
        ) if "args" in obj else ()
        return cls(
            op=op,
            sort=TermSort.from_data(obj["sort"], f"{field}.sort"),
            args=args,
            name=(
                _identifier(obj["name"], f"{field}.name")
                if "name" in obj
                else None
            ),
            index=(_nonnegative(obj["index"], f"{field}.index") if "index" in obj else None),
            bindings=(tuple(Declaration.from_data(d) for d in _array(obj["bindings"], f"{field}.bindings")) if "bindings" in obj else None),
            value=obj.get("value"),
            amount=(
                _nonnegative(obj["amount"], f"{field}.amount")
                if "amount" in obj
                else None
            ),
            hi=(
                _nonnegative(obj["hi"], f"{field}.hi")
                if "hi" in obj
                else None
            ),
            lo=(
                _nonnegative(obj["lo"], f"{field}.lo")
                if "lo" in obj
                else None
            ),
        )

def free_references(expressions: Iterable[TypedExpr]) -> dict[str | int, TermSort]:
    """Validate bound references and collect free names/positions, scope-aware."""
    result: dict[str | int, TermSort] = {}
    stack = [(node, ()) for node in expressions]
    visited: set[tuple[int, tuple[Declaration, ...]]] = set()
    while stack:
        node, scope = stack.pop()
        key = (id(node), scope)
        if key in visited:
            continue
        visited.add(key)
        if node.op == "var":
            bound = None
            if node.index is not None:
                if node.index < len(scope):
                    bound = scope[node.index]
                    ref: str | int = node.index
                else:
                    ref = node.index - len(scope)
            else:
                assert node.name is not None
                ref = node.name
                bound = next((d for d in scope if d.name == ref), None)
            if bound is not None:
                if bound.sort != node.sort:
                    raise ArtifactError("bound variable has wrong sort")
            elif result.setdefault(ref, node.sort) != node.sort:
                raise ArtifactError(f"inconsistent sort for {ref!r}")
        elif node.op == "let_par":
            assert node.bindings is not None
            stack.extend((rhs, scope) for rhs in node.args[:-1])
            stack.append((node.args[-1], node.bindings + scope))
        else:
            stack.extend((arg, scope) for arg in node.args)
    return result


def variable_sorts(expressions: Iterable[TypedExpr]) -> dict[str, TermSort]:
    """Free named variables. Positional terms require context-aware validation."""
    refs = free_references(expressions)
    if any(isinstance(ref, int) for ref in refs):
        raise ArtifactError("positional free variables require a declaration context")
    return {ref: sort for ref, sort in refs.items() if isinstance(ref, str)}
