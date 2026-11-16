"""Context- and sort-indexed QF_ABV STSes and interface adapters.

The marker C tracks a context statically; runtime declarations track its actual
names and widths. S is a concrete Bool/BV/Array sort witness. Python enforces
local structural invariants; the corresponding Lean definitions state laws.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Generic, TypeAlias, TypeVar

from .expr import BOOL, Declaration, TermSort, TypedExpr, free_references
from .fp import FPValue, RoundingMode
from .segments import Segment
from .sts import STS
from .substitution import substitute_exprs

C = TypeVar("C")
D = TypeVar("D")
E = TypeVar("E")

@dataclass(frozen=True)
class BoolSort:
    def encode(self) -> TermSort:
        return BOOL

@dataclass(frozen=True)
class BVSort:
    width: int
    def __post_init__(self) -> None:
        TermSort.bv(self.width)
    def encode(self) -> TermSort:
        return TermSort.bv(self.width)

@dataclass(frozen=True)
class ArraySort:
    index_width: int
    value_width: int
    def __post_init__(self) -> None:
        TermSort.array(self.index_width, self.value_width)
    def encode(self) -> TermSort:
        return TermSort.array(self.index_width, self.value_width)

@dataclass(frozen=True)
class FPSort:
    exponent_bits: int
    significand_bits: int
    def __post_init__(self) -> None:
        TermSort.fp(self.exponent_bits, self.significand_bits)
    def encode(self) -> TermSort:
        return TermSort.fp(self.exponent_bits, self.significand_bits)

@dataclass(frozen=True)
class RoundingModeSort:
    def encode(self) -> TermSort:
        return TermSort.rounding_mode()

Sort: TypeAlias = BoolSort | BVSort | ArraySort | FPSort | RoundingModeSort
S = TypeVar("S", bound=Sort, covariant=True)

def decode_sort(raw: TermSort) -> Sort:
    if raw.kind == "bool":
        return BoolSort()
    if raw.kind == "bv":
        assert raw.width is not None
        return BVSort(raw.width)
    if raw.kind == "fp":
        return FPSort(*raw.require_fp_widths())
    if raw.kind == "rm":
        return RoundingModeSort()
    assert raw.index_width is not None and raw.value_width is not None
    return ArraySort(raw.index_width, raw.value_width)

@dataclass(frozen=True)
class QFAbvContext(Generic[C]):
    declarations: tuple[Declaration, ...]

    def check_expression(self, node: TypedExpr) -> None:
        for ref, sort in free_references((node,)).items():
            declaration = (self.declarations[ref] if ref < len(self.declarations) else None) if isinstance(ref, int) else next((d for d in self.declarations if d.name == ref), None)
            if declaration is None or declaration.sort != sort:
                raise ValueError(f"variable {ref!r} absent or has wrong sort")

    def expression(self, node: TypedExpr, sort: S) -> QFAbvExpr[C, S]:
        return QFAbvExpr(self, sort, node)

@dataclass(frozen=True)
class QFAbvExpr(Generic[C, S]):
    context: QFAbvContext[C]
    sort: S
    node: TypedExpr

    def __post_init__(self) -> None:
        if self.sort.encode() != self.node.sort:
            raise ValueError("sort witness disagrees with expression")
        self.context.check_expression(self.node)

    def substitute(self, update: QFAbvUpdate[D, C]) -> QFAbvExpr[D, S]:
        if update.target != self.context:
            raise ValueError("substitution output context disagrees")
        node, = substitute_exprs((self.node,), update.replacements(), positional=tuple(e.node for e in update.rhs))
        return QFAbvExpr(update.source, self.sort, node)

@dataclass(frozen=True)
class QFAbvUpdate(Generic[C, D]):
    """Dense simultaneous assignment, ordered by output declarations.

    Every RHS reads only source C. Its position identifies the output variable
    in D; sibling RHSs never observe one another's writes.
    """
    source: QFAbvContext[C]
    target: QFAbvContext[D]
    rhs: tuple[QFAbvExpr[C, Sort], ...]

    def __post_init__(self) -> None:
        if len(self.rhs) != len(self.target.declarations):
            raise ValueError("update must assign every output declaration")
        for declaration, expression in zip(self.target.declarations, self.rhs):
            if expression.context != self.source:
                raise ValueError("RHS belongs to another input context")
            if expression.node.sort != declaration.sort:
                raise ValueError("RHS and output variable sorts disagree")

    def replacements(self) -> dict[str, TypedExpr]:
        result = {}
        for d, e in zip(self.target.declarations, self.rhs):
            result.setdefault(d.name, e.node)
        return result

    @classmethod
    def identity(cls, context: QFAbvContext[C]) -> QFAbvUpdate[C, C]:
        return QFAbvUpdate(context, context, tuple(
            QFAbvExpr(context, decode_sort(d.sort), TypedExpr.at(i, d.sort))
            for i, d in enumerate(context.declarations)))

    def compose(self, right: QFAbvUpdate[D, E]) -> QFAbvUpdate[C, E]:
        if self.target != right.source:
            raise ValueError("updates have incompatible middle contexts")
        nodes = substitute_exprs(tuple(e.node for e in right.rhs),
                                 self.replacements(), positional=tuple(e.node for e in self.rhs))
        return QFAbvUpdate(self.source, right.target, tuple(
            QFAbvExpr(self.source, expression.sort, node)
            for expression, node in zip(right.rhs, nodes)))

def _compose_guarded(
    left_guard: QFAbvExpr[C, BoolSort], left_update: QFAbvUpdate[C, D],
    right_guard: QFAbvExpr[D, BoolSort], right_update: QFAbvUpdate[D, E],
) -> tuple[QFAbvExpr[C, BoolSort], QFAbvUpdate[C, E]]:
    """Compose both the guard and the simultaneous update."""
    update = left_update.compose(right_update)
    lifted = right_guard.substitute(left_update)
    guard = TypedExpr.conjoin(left_guard.node, lifted.node)
    return QFAbvExpr(update.source, BoolSort(), guard), update


@dataclass(frozen=True)
class QFAbvStep(Generic[C]):
    """A guarded transition within one state context."""
    guard: QFAbvExpr[C, BoolSort]
    update: QFAbvUpdate[C, C]

    def __post_init__(self) -> None:
        if self.guard.context != self.update.source or self.guard.node.sort != BOOL:
            raise ValueError("guard must be Bool over the update input context")
        if self.update.source != self.update.target:
            raise ValueError("step input and output contexts must match")

    @classmethod
    def identity(cls, context: QFAbvContext[C]) -> QFAbvStep[C]:
        return QFAbvStep(QFAbvExpr(context, BoolSort(), TypedExpr.bool_lit(True)),
                         QFAbvUpdate[C, C].identity(context))

    def compose(self, right: QFAbvStep[C]) -> QFAbvStep[C]:
        if not isinstance(right, QFAbvStep):
            raise TypeError("compose expects a step; use compose_adapter for an adapter")
        return QFAbvStep(*_compose_guarded(self.guard, self.update, right.guard, right.update))

    def to_adapter(self) -> QFAbvAdapter[C, C]:
        return QFAbvAdapter(self.guard, self.update)

    def compose_adapter(self, right: QFAbvAdapter[C, D]) -> QFAbvAdapter[C, D]:
        if not isinstance(right, QFAbvAdapter):
            raise TypeError("compose_adapter expects an adapter")
        return QFAbvAdapter(*_compose_guarded(self.guard, self.update, right.guard, right.update))


@dataclass(frozen=True)
class QFAbvAdapter(Generic[C, D]):
    """A guarded translation between state contexts, distinct from a step."""
    guard: QFAbvExpr[C, BoolSort]
    update: QFAbvUpdate[C, D]

    def __post_init__(self) -> None:
        if self.guard.context != self.update.source or self.guard.node.sort != BOOL:
            raise ValueError("guard must be Bool over the update input context")

    @classmethod
    def identity(cls, context: QFAbvContext[C]) -> QFAbvAdapter[C, C]:
        return QFAbvAdapter(QFAbvExpr(context, BoolSort(), TypedExpr.bool_lit(True)),
                            QFAbvUpdate.identity(context))

    def compose(self, right: QFAbvAdapter[D, E]) -> QFAbvAdapter[C, E]:
        if not isinstance(right, QFAbvAdapter):
            raise TypeError("compose expects an adapter; use compose_step for a step")
        return QFAbvAdapter(*_compose_guarded(self.guard, self.update, right.guard, right.update))

    def compose_step(self, right: QFAbvStep[D]) -> QFAbvAdapter[C, D]:
        if not isinstance(right, QFAbvStep):
            raise TypeError("compose_step expects a step")
        return QFAbvAdapter(*_compose_guarded(self.guard, self.update, right.guard, right.update))

@dataclass(frozen=True)
class QFAbvArrayValue:
    """A finite-support valuation of a total BV-indexed array."""
    sort: ArraySort
    default: int
    entries: tuple[tuple[int, int], ...] = ()

    def __post_init__(self) -> None:
        if type(self.default) is not int or not 0 <= self.default < (1 << self.sort.value_width):
            raise ValueError("array default outside element sort")
        indices = tuple(index for index, _ in self.entries)
        if indices != tuple(sorted(set(indices))):
            raise ValueError("array entries must have unique sorted indices")
        for index, value in self.entries:
            if (type(index) is not int or type(value) is not int
                    or not 0 <= index < (1 << self.sort.index_width)
                    or not 0 <= value < (1 << self.sort.value_width)
                    or value == self.default):
                raise ValueError("array entry outside canonical finite support")

Value: TypeAlias = bool | int | QFAbvArrayValue | FPValue | RoundingMode

@dataclass(frozen=True)
class QFAbvValuation(Generic[C]):
    context: QFAbvContext[C]
    values: tuple[Value, ...]

    def __post_init__(self) -> None:
        if len(self.values) != len(self.context.declarations):
            raise ValueError("valuation must provide every declaration")
        for declaration, value in zip(self.context.declarations, self.values):
            sort = declaration.sort
            if sort.kind == "bool":
                valid = type(value) is bool
            elif sort.kind == "bv":
                assert sort.width is not None
                valid = type(value) is int and 0 <= value < (1 << sort.width)
            elif sort.kind == "fp":
                valid = isinstance(value, FPValue) and value.sort == sort
            elif sort.kind == "rm":
                valid = isinstance(value, RoundingMode)
            else:
                valid = isinstance(value, QFAbvArrayValue) and value.sort.encode() == sort
            if not valid:
                raise ValueError(f"value has wrong sort for {declaration.name}")

@dataclass(frozen=True)
class QFAbvSTS(Generic[C]):
    """All state, including PC/control, belongs to this one context."""
    context: QFAbvContext[C]
    steps: tuple[QFAbvStep[C], ...]

    def __post_init__(self) -> None:
        for step in self.steps:
            if not isinstance(step, QFAbvStep) or step.update.source != self.context:
                raise ValueError("STS step does not use its full state context")

    def to_sts(self) -> STS[QFAbvValuation[C], QFAbvStep[C]]:
        return STS(self.steps)

QFAbvSegment: TypeAlias = Segment[
    QFAbvValuation[C], QFAbvValuation[D], QFAbvValuation[E],
    QFAbvStep[D], QFAbvAdapter[C, D], QFAbvAdapter[D, E]]
@dataclass(frozen=True)
class QFAbvControlView(Generic[C, S]):
    """Optional typed expression projecting existing state control."""
    projection: QFAbvExpr[C, S]
