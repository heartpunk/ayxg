import Ayxg.QfAbv.Step
import Ayxg.LTS.QfAbv.SymbolicTransitionSystem

namespace Ayxg.QfAbv

variable [FPInterpretation]

open _root_.Ayxg.LTS.QfAbv

/-- Embed one whole-state QF_ABV transformer as an edge at the sole structural
control site. Any program counter or error state remains in the environment. -/
def QFAbvStep.toControlEdge {Γ : Ctx} (step : QFAbvStep Γ Γ) :
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition Unit Γ where
  src := ()
  tgt := none
  label := { guard := step.guard, update := step.update }

/-- View a finite list of whole-state transformers through the preferred
source-indexed symbolic transition system. -/
def toControlSystem {Γ : Ctx} (steps : List (QFAbvStep Γ Γ)) :
    _root_.Ayxg.LTS.QfAbv.SymbolicTransitionSystem Unit Γ
      (_root_.Ayxg.LTS.QfAbv.SymbolicTransition Unit Γ) :=
  _root_.Ayxg.LTS.QfAbv.SymbolicTransitionSystem.legacy
    (fun _ => steps.map QFAbvStep.toControlEdge)

private theorem toControlEdge_injective {Γ : Ctx} :
    Function.Injective (QFAbvStep.toControlEdge (Γ := Γ)) := by
  intro a b h
  cases a with
  | mk agu aup =>
    cases b with
    | mk bgu bup =>
      cases h
      rfl

/-- A converted edge occurs precisely when its original transformer occurs. -/
theorem toControlEdge_mem_iff {Γ : Ctx}
    (steps : List (QFAbvStep Γ Γ)) (step : QFAbvStep Γ Γ) :
    QFAbvStep.toControlEdge step ∈ (toControlSystem steps).transAt () ↔
      step ∈ steps := by
  change QFAbvStep.toControlEdge step ∈ steps.map QFAbvStep.toControlEdge ↔
    step ∈ steps
  constructor
  · intro h
    obtain ⟨original, hmem, heq⟩ := List.mem_map.mp h
    have hs : original = step := toControlEdge_injective heq
    exact hs ▸ hmem
  · intro h
    exact List.mem_map.mpr ⟨step, h, rfl⟩

/-- The converted edge has exactly the original guard/update denotation. -/
theorem toControlEdge_denotes_iff {Γ : Ctx} (step : QFAbvStep Γ Γ)
    (source target : Env Γ) :
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition.denotes
      (QFAbvStep.toControlEdge step) ⟨(), source⟩ ⟨(), target⟩ ↔
      step.denotes source target := by
  simp [QFAbvStep.denotes,
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition.denotes,
    _root_.Ayxg.LTS.QfAbv.SymbolicEdgeSemantics.denotes,
    _root_.Ayxg.LTS.QfAbv.SymbolicEdgeSemantics.nextConfig,
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition.edgeSemantics,
    QFAbvStep.toControlEdge]

/-- Exact labeled correspondence between a list entry and its source-indexed
edge. The complete source and target environments are retained. -/
theorem toControlSystem_step_iff {Γ : Ctx}
    (steps : List (QFAbvStep Γ Γ)) (step : QFAbvStep Γ Γ)
    (source target : Env Γ) :
    (step ∈ steps ∧ step.denotes source target) ↔
      (toControlSystem steps).toLTS.Tr ⟨(), source⟩
        (QFAbvStep.toControlEdge step) ⟨(), target⟩ := by
  change (step ∈ steps ∧ step.denotes source target) ↔
    (QFAbvStep.toControlEdge step ∈ (toControlSystem steps).transAt () ∧
      _root_.Ayxg.LTS.QfAbv.SymbolicTransition.denotes
        (QFAbvStep.toControlEdge step) ⟨(), source⟩ ⟨(), target⟩)
  rw [toControlEdge_mem_iff, toControlEdge_denotes_iff]

end Ayxg.QfAbv
