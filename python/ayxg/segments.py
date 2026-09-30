"""Reusable interfaces around STSes, with a DAG of segment containment."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Generic, Hashable, TypeVar
from .sts import STS

Input = TypeVar("Input")
Body = TypeVar("Body")
Output = TypeVar("Output")
Label = TypeVar("Label")
EntryLabel = TypeVar("EntryLabel")
ExitLabel = TypeVar("ExitLabel")
NodeId = TypeVar("NodeId", bound=Hashable)
SegmentType = TypeVar("SegmentType")
ViewSyntax = TypeVar("ViewSyntax")
Control = TypeVar("Control")

@dataclass(frozen=True)
class Adapter(Generic[Input, Output, Label]):
    """Structured syntax for a relation between two interface state types."""
    label: Label

@dataclass(frozen=True)
class Segment(Generic[Input, Body, Output, Label, EntryLabel, ExitLabel]):
    input: Adapter[Input, Body, EntryLabel]
    body: STS[Body, Label]
    exits: tuple[Adapter[Body, Output, ExitLabel], ...]

@dataclass(frozen=True)
class ControlView(Generic[Body, Control, ViewSyntax]):
    """Optional projection syntax into existing state, not separate control."""
    projection: ViewSyntax

@dataclass(frozen=True)
class SegmentNode(Generic[NodeId, SegmentType]):
    key: NodeId
    segment: SegmentType
    children: tuple[NodeId, ...] = ()

@dataclass(frozen=True)
class SegmentDAG(Generic[NodeId, SegmentType]):
    """Shared children are referenced, not copied.

    Child-before-parent order witnesses acyclicity of containment. Execution
    loops and branches remain transitions inside each segment's STS.
    """
    nodes: tuple[SegmentNode[NodeId, SegmentType], ...]
    roots: tuple[NodeId, ...]

    def __post_init__(self) -> None:
        seen: set[NodeId] = set()
        for node in self.nodes:
            if node.key in seen:
                raise ValueError("duplicate segment key")
            if any(child not in seen for child in node.children):
                raise ValueError("segment children must precede their parent")
            seen.add(node.key)
        if any(root not in seen for root in self.roots):
            raise ValueError("unknown segment root")
