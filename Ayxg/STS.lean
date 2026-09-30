import Ayxg.LTS

namespace Ayxg

/-- Finite transition syntax over complete implementation states.
Interpretation is separate from syntax; control is already part of `State`. -/
structure STS (State Label : Type) where
  steps : List Label

namespace STS

/-- Interpret structured labels as the existing generic relational LTS. -/
def toLTS {State Label : Type} (model : STS State Label)
    (semantics : State → Label → State → Prop) : LTS State Label where
  Tr := fun source label target => label ∈ model.steps ∧ semantics source label target

/-- Zero or more body transitions, with explicit endpoint states. -/
def Runs {State Label : Type} (model : STS State Label)
    (semantics : State → Label → State → Prop) (source target : State) : Prop :=
  (model.toLTS semantics).ReachableFrom source target

/-- Law statement for concatenating finite runs. -/
def runsTransitiveLaw {State Label : Type} (model : STS State Label)
    (semantics : State → Label → State → Prop) : Prop :=
  ∀ a b c, model.Runs semantics a b → model.Runs semantics b c → model.Runs semantics a c

end STS

/-- Structured adapter label between two state types. -/
structure Adapter (Input Output Label : Type) where
  label : Label

namespace Adapter

def denotes {Input Output Label : Type} (adapter : Adapter Input Output Label)
    (semantics : Input → Label → Output → Prop) (i : Input) (o : Output) : Prop :=
  semantics i adapter.label o

end Adapter

/-- A reusable interface: input glue, an STS body, and guarded output glue. -/
structure Segment (Input Body Output Label EntryLabel ExitLabel : Type) where
  input : Adapter Input Body EntryLabel
  body : STS Body Label
  exits : List (Adapter Body Output ExitLabel)

namespace Segment

/-- Segment denotation allows an empty body run; adapter labels select entry/exit. -/
def denotes {Input Body Output Label EntryLabel ExitLabel : Type}
    (segment : Segment Input Body Output Label EntryLabel ExitLabel)
    (entrySemantics : Input → EntryLabel → Body → Prop)
    (bodySemantics : Body → Label → Body → Prop)
    (exitSemantics : Body → ExitLabel → Output → Prop)
    (i : Input) (o : Output) : Prop :=
  ∃ first last, segment.input.denotes entrySemantics i first
    ∧ segment.body.Runs bodySemantics first last
    ∧ ∃ exit ∈ segment.exits, exit.denotes exitSemantics last o

end Segment

/-- Optional syntax describing a projection into existing state. -/
structure ControlView (State Control ViewSyntax : Type) where
  projection : ViewSyntax

namespace ControlView

def observe {State Control ViewSyntax : Type}
    (view : ControlView State Control ViewSyntax)
    (semantics : ViewSyntax → State → Control) (state : State) : Control :=
  semantics view.projection state

end ControlView

/-- Existential packaging permits different interface types in one hierarchy. -/
structure PackedSegment where
  Input : Type
  Body : Type
  Output : Type
  Label : Type
  EntryLabel : Type
  ExitLabel : Type
  value : Segment Input Body Output Label EntryLabel ExitLabel

structure SegmentNode (Id : Type u) (Payload : Type v) where
  key : Id
  segment : Payload
  children : List Id

namespace SegmentNode

/-- A topological enumeration: children precede parents and keys are unique. -/
def Ordered {Id : Type u} {Payload : Type v} (seen : List Id) :
    List (SegmentNode Id Payload) → Prop
  | [] => True
  | node :: rest => node.key ∉ seen
      ∧ (∀ child ∈ node.children, child ∈ seen)
      ∧ Ordered (node.key :: seen) rest

end SegmentNode

/-- The hierarchy records containment/reuse, never a second execution language.
The same child may be referenced by any number of later parents. -/
structure SegmentDAG (Id : Type u) (Payload : Type v) where
  nodes : List (SegmentNode Id Payload)
  roots : List Id
  ordered : SegmentNode.Ordered [] nodes
  rootsPresent : ∀ root ∈ roots, ∃ node ∈ nodes, node.key = root

end Ayxg
