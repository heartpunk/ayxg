"""WRUH's QF_ABV expression syntax, imported by ast-grep declaration spans.

This syntax is the let-free, positive-width, canonical-literal subset of
Ayxg.QfAbv.Expr. Context membership is provided by ayxg.qfabv.QFAbvExpr.
"""
from __future__ import annotations
from dataclasses import dataclass
import re
from typing import Any, Iterable, Mapping, cast

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
    if not isinstance(value, str) or not _ID_RE.fullmatch(value):
        raise ArtifactError(f"{field} is not a canonical identifier")
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

    def __post_init__(self) -> None:
        if self.kind == "bool":
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

    def require_bv_width(self) -> int:
        if self.kind != "bv" or self.width is None:
            raise ArtifactError("expected bit-vector sort")
        return self.width

    def require_array_widths(self) -> tuple[int, int]:
        if self.kind != "array" or self.index_width is None or self.value_width is None:
            raise ArtifactError("expected array sort")
        return self.index_width, self.value_width

    def to_data(self) -> dict[str, Any]:
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
    value: bool | int | None = None
    amount: int | None = None
    hi: int | None = None
    lo: int | None = None

    def __post_init__(self) -> None:
        expected_metadata: set[str]
        if self.op == "var":
            expected_metadata = {"name"}
            _identifier(self.name, "expression.name")
            self._require_arity(0)
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
                or self.amount <= 0
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
        result: dict[str, Any] = {
            "op": self.op,
            "sort": self.sort.to_data(),
        }
        if self.args:
            result["args"] = [arg.to_data() for arg in self.args]
        if self.name is not None:
            result["name"] = self.name
        if self.value is not None:
            result["value"] = self.value
        if self.amount is not None:
            result["amount"] = self.amount
        if self.hi is not None:
            result["hi"] = self.hi
        if self.lo is not None:
            result["lo"] = self.lo
        return result

    @classmethod
    def from_data(
        cls,
        value: Any,
        field: str = "expression",
    ) -> TypedExpr:
        obj = _object(value, field)
        op = _text(obj.get("op"), f"{field}.op")
        expected = {"op", "sort"}
        if op in {"var"}:
            expected.add("name")
        elif op in {"bool_lit", "bv_lit"}:
            expected.add("value")
        elif op in _EXTEND_OPS:
            expected |= {"args", "amount"}
        elif op == "extract":
            expected |= {"args", "hi", "lo"}
        elif op not in {"var", "bool_lit", "bv_lit"}:
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

def variable_sorts(expressions: Iterable[TypedExpr]) -> dict[str, TermSort]:
    """Collect variable sorts while expanding each shared DAG node once."""

    result: dict[str, TermSort] = {}
    stack = list(expressions)
    visited: set[int] = set()
    while stack:
        expression = stack.pop()
        identity = id(expression)
        if identity in visited:
            continue
        visited.add(identity)
        if expression.op == "var":
            prior = result.setdefault(_identifier(expression.name, "expression.name"), expression.sort)
            if prior != expression.sort:
                raise ArtifactError(
                    f"inconsistent sort for {expression.name}: "
                    "variable occurs at conflicting sorts"
                )
        stack.extend(expression.args)
    return result
