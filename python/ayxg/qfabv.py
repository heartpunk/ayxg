"""Context- and sort-indexed QF_ABV STSes and interface adapters.

The marker C tracks a context statically; runtime declarations track its actual
names and widths. S is a concrete Bool/BV/Array sort witness. Python enforces
local structural invariants; the corresponding Lean definitions state laws.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Generic, TypeAlias, TypeVar
from .expr import BOOL, Declaration, TermSort, TypedExpr, variable_sorts
from .substitution import substitute_exprs
from .sts import STS
from .segments import Adapter, Segment

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

Sort: TypeAlias = BoolSort | BVSort | ArraySort
S = TypeVar("S", bound=Sort, covariant=True)

def decode_sort(raw: TermSort) -> Sort:
    if raw.kind == "bool":
        return BoolSort()
    if raw.kind == "bv":
        assert raw.width is not None
        return BVSort(raw.width)
    assert raw.index_width is not None and raw.value_width is not None
    return ArraySort(raw.index_width, raw.value_width)

@dataclass(frozen=True)
class QFAbvContext(Generic[C]):
    declarations: tuple[Declaration, ...]

    def __post_init__(self) -> None:
        if len({d.name for d in self.declarations}) != len(self.declarations):
            raise ValueError("context declaration names must be unique")

    def check_expression(self, node: TypedExpr) -> None:
        sorts = {d.name: d.sort for d in self.declarations}
        for name, sort in variable_sorts((node,)).items():
            if sorts.get(name) != sort:
                raise ValueError(f"variable {name!r} absent or has wrong sort")

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
        node, = substitute_exprs((self.node,), update.replacements())
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
        return {d.name: e.node for d, e in zip(self.target.declarations, self.rhs)}

    @classmethod
    def identity(cls, context: QFAbvContext[C]) -> QFAbvUpdate[C, C]:
        return QFAbvUpdate(context, context, tuple(
            QFAbvExpr(context, decode_sort(d.sort), TypedExpr.var(d.name, d.sort))
            for d in context.declarations))

    def compose(self, right: QFAbvUpdate[D, E]) -> QFAbvUpdate[C, E]:
        if self.target != right.source:
            raise ValueError("updates have incompatible middle contexts")
        nodes = substitute_exprs(tuple(e.node for e in right.rhs),
                                 self.replacements())
        return QFAbvUpdate(self.source, right.target, tuple(
            QFAbvExpr(self.source, expression.sort, node)
            for expression, node in zip(right.rhs, nodes)))

@dataclass(frozen=True)
class QFAbvStep(Generic[C, D]):
    guard: QFAbvExpr[C, BoolSort]
    update: QFAbvUpdate[C, D]

    def __post_init__(self) -> None:
        if self.guard.context != self.update.source or self.guard.node.sort != BOOL:
            raise ValueError("guard must be Bool over the update input context")

    @classmethod
    def identity(cls, context: QFAbvContext[C]) -> QFAbvStep[C, C]:
        return QFAbvStep(QFAbvExpr(context, BoolSort(), TypedExpr.bool_lit(True)),
                         QFAbvUpdate[C, C].identity(context))

    def compose(self, right: QFAbvStep[D, E]) -> QFAbvStep[C, E]:
        update = self.update.compose(right.update)
        lifted = right.guard.substitute(self.update)
        guard = TypedExpr.conjoin(self.guard.node, lifted.node)
        return QFAbvStep(QFAbvExpr(update.source, BoolSort(), guard), update)

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

Value: TypeAlias = bool | int | QFAbvArrayValue

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
            else:
                valid = isinstance(value, QFAbvArrayValue) and value.sort.encode() == sort
            if not valid:
                raise ValueError(f"value has wrong sort for {declaration.name}")

@dataclass(frozen=True)
class QFAbvSTS(Generic[C]):
    """All state, including PC/control, belongs to this one context."""
    context: QFAbvContext[C]
    steps: tuple[QFAbvStep[C, C], ...]

    def __post_init__(self) -> None:
        for step in self.steps:
            if step.update.source != self.context or step.update.target != self.context:
                raise ValueError("STS step does not use its full state context")

    def to_sts(self) -> STS[QFAbvValuation[C], QFAbvStep[C, C]]:
        return STS(self.steps)

QFAbvAdapter: TypeAlias = Adapter[QFAbvValuation[C], QFAbvValuation[D], QFAbvStep[C, D]]
QFAbvSegment: TypeAlias = Segment[
    QFAbvValuation[C], QFAbvValuation[D], QFAbvValuation[E],
    QFAbvStep[D, D], QFAbvStep[C, D], QFAbvStep[D, E]]
@dataclass(frozen=True)
class QFAbvControlView(Generic[C, S]):
    """Optional typed expression projecting existing state control."""
    projection: QFAbvExpr[C, S]
