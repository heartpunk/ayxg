"""Generic STS syntax and its interpretation boundary.

State contains the entire implementation state, including control. Label data
is interpreted by implemented primitives; opaque callbacks are not model data.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Generic, Protocol, TypeVar

State = TypeVar("State")
Label = TypeVar("Label")
SourceContra = TypeVar("SourceContra", contravariant=True)
LabelContra = TypeVar("LabelContra", contravariant=True)
TargetContra = TypeVar("TargetContra", contravariant=True)

class RelationSemantics(Protocol[SourceContra, LabelContra, TargetContra]):
    """Implementation of primitive syntax semantics; Lean states its laws."""
    def denotes(self, source: SourceContra, label: LabelContra,
                target: TargetContra, /) -> bool: ...

@dataclass(frozen=True)
class STS(Generic[State, Label]):
    """Finite transition labels, interpreted over complete states."""
    steps: tuple[Label, ...]

    def denotes(self, source: State, label: Label, target: State,
                semantics: RelationSemantics[State, Label, State]) -> bool:
        return label in self.steps and semantics.denotes(source, label, target)
