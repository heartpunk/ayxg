import Ayxg.LTS
import Ayxg.LTS.QfAbv.SymbolicTransition

namespace Ayxg
namespace LTS
namespace QfAbv

variable [_root_.Ayxg.QfAbv.FPInterpretation]

open _root_.Ayxg.QfAbv

/-- Source-keyed symbolic transition system over a typed QF_ABV environment.

This is the active QF_ABV transition-system layer: control sites map to
symbolic edges whose labels carry guard/update transformer payloads. Its LTS
view is direct; there is no intermediate concrete machine layer. -/
structure SymbolicTransitionSystem (C : Type) (Γ : Ctx) (E : Type) where
  edgeSemantics : SymbolicEdgeSemantics C Γ E
  transAt : C → List E

namespace SymbolicTransitionSystem

/-- Canonical constructor for an STS over legacy `SymbolicTransition` edges. -/
def legacy {C : Type} {Γ : Ctx}
    (transAt : C → List (SymbolicTransition C Γ)) :
    SymbolicTransitionSystem C Γ (SymbolicTransition C Γ) where
  edgeSemantics := SymbolicTransition.edgeSemantics
  transAt := transAt

/-- LTS view whose labels are the symbolic transition edges themselves.

A step is labeled by a symbolic edge from the current control site whose
guard/update semantics relate the endpoint states. -/
def toLTS {C : Type} {Γ : Ctx} {E : Type}
    (m : SymbolicTransitionSystem C Γ E) :
    _root_.Ayxg.LTS (Config C Γ) E where
  Tr := fun s edge s' =>
    edge ∈ m.transAt s.control ∧ m.edgeSemantics.denotes edge s s'

/-- Data-level witness for one symbolic transition-system step. -/
structure StepWitness {C : Type} {Γ : Ctx} {E : Type}
    (m : SymbolicTransitionSystem C Γ E)
    (s t : Config C Γ) : Type where
  label : E
  mem : label ∈ m.transAt s.control
  denotes : m.edgeSemantics.denotes label s t

/-- Data-level witness for a symbolic transition-system run.

The label list is preserved as data, while the witness also threads every
intermediate state through the constructor indices. -/
inductive Run {C : Type} {Γ : Ctx} {E : Type}
    (m : SymbolicTransitionSystem C Γ E) :
    Config C Γ → List E → Config C Γ → Type where
  | nil : Run m s [] s
  | cons : (step : StepWitness m s mid) → Run m mid labels t →
      Run m s (step.label :: labels) t

namespace Run

/-- A data-level symbolic run certifies a symbolic LTS trace. -/
theorem toTrace {C : Type} {Γ : Ctx} {E : Type}
    {m : SymbolicTransitionSystem C Γ E}
    {s t : Config C Γ} {labels : List E}
    (run : Run m s labels t) : m.toLTS.IsTrace s labels t := by
  induction run with
  | nil => exact _root_.Ayxg.LTS.IsTrace.nil _
  | cons step _ ih =>
      exact _root_.Ayxg.LTS.IsTrace.cons step.label _ ⟨step.mem, step.denotes⟩ ih

/-- Every symbolic LTS trace has a corresponding data-level symbolic run
witness.

This goes from `Prop` to `Prop` (`Nonempty`), not from `Prop` to computational
data: it proves existence of a run without extracting one for execution. -/
theorem exists_of_trace {C : Type} {Γ : Ctx} {E : Type}
    {m : SymbolicTransitionSystem C Γ E}
    {s t : Config C Γ} {labels : List E}
    (trace : m.toLTS.IsTrace s labels t) : Nonempty (Run m s labels t) := by
  induction trace with
  | nil s => exact ⟨Run.nil⟩
  | cons label labels hstep _ ih =>
      rcases hstep with ⟨hmem, hdenotes⟩
      rcases ih with ⟨tailRun⟩
      exact ⟨Run.cons { label := label, mem := hmem, denotes := hdenotes } tailRun⟩

/-- A nonempty data-level symbolic run induces nonempty denotation of the
sequence of symbolic labels over the endpoint environments. -/
theorem toDenotesNonempty {C : Type} {Γ : Ctx} {E : Type}
    {m : SymbolicTransitionSystem C Γ E} :
    {s t : Config C Γ} → {head : E} →
    {tail : List E} → Run m s (head :: tail) t →
      SymbolicLabel.DenotesNonempty (m.edgeSemantics.symbolicLabel head)
        (tail.map m.edgeSemantics.symbolicLabel) s.env t.env
  | _, _, _, [], Run.cons step Run.nil =>
      SymbolicLabel.DenotesNonempty.single
        (SymbolicEdgeSemantics.denotes_symbolicLabel step.denotes)
  | _, _, _, next :: rest, Run.cons step tailRun =>
      SymbolicLabel.DenotesNonempty.cons
        (SymbolicEdgeSemantics.denotes_symbolicLabel step.denotes)
        (toDenotesNonempty tailRun)

/-- A nonempty data-level symbolic run's composed label denotes the endpoint
environments. -/
theorem composedLabel_denotes {C : Type} {Γ : Ctx} {E : Type}
    {m : SymbolicTransitionSystem C Γ E}
    {s t : Config C Γ} {head : E}
    {tail : List E} (run : Run m s (head :: tail) t) :
    (SymbolicLabel.composeNonempty (m.edgeSemantics.symbolicLabel head)
      (tail.map m.edgeSemantics.symbolicLabel)).denotes s.env t.env :=
  (SymbolicLabel.denotes_composeNonempty_iff (m.edgeSemantics.symbolicLabel head)
    (tail.map m.edgeSemantics.symbolicLabel) s.env t.env).2 (toDenotesNonempty run)

/-- A nonempty symbolic LTS trace's composed label denotes the endpoint
environments. -/
theorem trace_composedLabel_denotes {C : Type} {Γ : Ctx} {E : Type}
    {m : SymbolicTransitionSystem C Γ E} {s t : Config C Γ}
    {head : E} {tail : List E}
    (trace : m.toLTS.IsTrace s (head :: tail) t) :
    (SymbolicLabel.composeNonempty (m.edgeSemantics.symbolicLabel head)
      (tail.map m.edgeSemantics.symbolicLabel)).denotes s.env t.env := by
  rcases exists_of_trace trace with ⟨run⟩
  exact composedLabel_denotes run

end Run

/-- Source-keyed well-formedness for symbolic transition systems. -/
def WellFormed {C : Type} {Γ : Ctx} {E : Type}
    (m : SymbolicTransitionSystem C Γ E) : Prop :=
  ∀ c edge, edge ∈ m.transAt c → m.edgeSemantics.source edge = c

/-- Membership in a well-formed source bucket determines the edge source. -/
theorem transAt_mem_src {C : Type} {Γ : Ctx} {E : Type}
    {m : SymbolicTransitionSystem C Γ E}
    (hWF : m.WellFormed) {c : C} {edge : E}
    (hmem : edge ∈ m.transAt c) : m.edgeSemantics.source edge = c :=
  hWF c edge hmem

end SymbolicTransitionSystem

end QfAbv
end LTS
end Ayxg
