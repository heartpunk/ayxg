import Ayxg.LTS.QfAbv.SymbolicTransitionSystem
import Ayxg.QfAbv.Step
import Init.ShareCommon

namespace Ayxg.LTS.QfAbv.SymbolicTransitionSystem

open _root_.Ayxg.QfAbv

variable [FPInterpretation]

/-- One symbolic successor keeps the source transition label alongside the
composed guard/update step. -/
structure SymbolicSuccessor (E : Type) (Γinput Γ : Ctx) where
  edge : E
  step : QFAbvStep Γinput Γ

/-- Voogd stepping for a unit-control source-indexed system. Every returned
successor retains the exact source edge that produced it. -/
def symbolicStep {Γinput Γ : Ctx} {E : Type}
    (model : SymbolicTransitionSystem Unit Γ E)
    (input : QFAbvStep Γinput Γ) : List (SymbolicSuccessor E Γinput Γ) :=
  ShareCommon.shareCommon' <|
    (model.transAt ()).map fun edge =>
      { edge, step := input.compose
          (QFAbvStep.ofSymbolicLabel (model.edgeSemantics.symbolicLabel edge)) }

/-- Regard an already constructed list of labeled symbolic successors as an
STS whose control is `Unit` and whose state transformer is the successor's
complete QF_ABV step. -/
def ofSymbolicSuccessors {Γ : Ctx} {E : Type}
    (successors : List (SymbolicSuccessor E Γ Γ)) :
    SymbolicTransitionSystem Unit Γ (SymbolicSuccessor E Γ Γ) where
  edgeSemantics := {
    source := fun _ => ()
    symbolicLabel := fun successor =>
      ⟨successor.step.guard, successor.step.update⟩
    nextControl := fun _ _ => ()
  }
  transAt := fun _ => successors

/-- Packaging symbolic successors preserves exactly their membership and
complete guarded state-transformer semantics. -/
theorem ofSymbolicSuccessors_transition_iff {Γ : Ctx} {E : Type}
    (successors : List (SymbolicSuccessor E Γ Γ))
    (source target : Config Unit Γ) (successor : SymbolicSuccessor E Γ Γ) :
    (ofSymbolicSuccessors successors).toLTS.Tr source successor target ↔
      successor ∈ successors ∧ successor.step.denotes source.env target.env := by
  cases source with
  | mk sourceControl sourceEnv =>
    cases sourceControl
    cases target with
    | mk targetControl targetEnv =>
      cases targetControl
      simp only [ofSymbolicSuccessors, SymbolicTransitionSystem.toLTS,
        SymbolicEdgeSemantics.denotes, SymbolicEdgeSemantics.nextConfig,
        QFAbvStep.denotes, true_and, Config.mk.injEq]

/-- Exact connection between each returned labeled successor and the
source-indexed LTS transition relation, with the label preserved. -/
theorem symbolicStep_denotes_iff {Γinput Γ : Ctx} {E : Type}
    (model : SymbolicTransitionSystem Unit Γ E)
    (input : QFAbvStep Γinput Γ) (ρ : Env Γinput) (edge : E) (target : Env Γ) :
    (∃ successor ∈ model.symbolicStep input,
      successor.edge = edge ∧ successor.step.denotes ρ target) ↔
      Eval.evalBool ρ input.guard = true ∧
        model.toLTS.Tr ⟨(), input.update.eval ρ⟩ edge ⟨(), target⟩ := by
  simp only [symbolicStep, ShareCommon.shareCommon', List.mem_map]
  constructor
  · rintro ⟨successor, ⟨sourceEdge, member, rfl⟩, hedge, denotes⟩
    simp only at hedge
    subst sourceEdge
    obtain ⟨middle, hinput, hmodel⟩ :=
      (QFAbvStep.compose_denotes_iff input
        (QFAbvStep.ofSymbolicLabel (model.edgeSemantics.symbolicLabel edge))
        ρ target).1 denotes
    rcases hinput with ⟨hguard, hupdate⟩
    subst middle
    change Eval.evalBool (input.update.eval ρ)
        (model.edgeSemantics.symbolicLabel edge).guard = true ∧
      (model.edgeSemantics.symbolicLabel edge).update.eval
        (input.update.eval ρ) = target at hmodel
    have hdenotes : model.edgeSemantics.denotes edge
        ⟨(), input.update.eval ρ⟩ ⟨(), target⟩ := by
      refine ⟨rfl, hmodel.1, ?_⟩
      cases hnext : model.edgeSemantics.nextControl edge
          ⟨(), input.update.eval ρ⟩ with
      | unit =>
        simp [SymbolicEdgeSemantics.nextConfig, hnext, hmodel.2]
    exact ⟨hguard, ⟨member, hdenotes⟩⟩
  · rintro ⟨hguard, htransition⟩
    rcases htransition with ⟨member, hdenotes⟩
    rcases hdenotes with ⟨_, hedgeGuard, hnext⟩
    have hlabel : (model.edgeSemantics.symbolicLabel edge).denotes
        (input.update.eval ρ) target := by
      refine ⟨hedgeGuard, ?_⟩
      change model.edgeSemantics.nextConfig edge
        ⟨(), input.update.eval ρ⟩ = ⟨(), target⟩ at hnext
      have hcontrol : model.edgeSemantics.nextControl edge
          ⟨(), input.update.eval ρ⟩ = () := Subsingleton.elim _ _
      have henv := congrArg Config.env hnext
      simpa [SymbolicEdgeSemantics.nextConfig, hcontrol] using henv
    have hcomposed := (QFAbvStep.compose_denotes_iff input
      (QFAbvStep.ofSymbolicLabel (model.edgeSemantics.symbolicLabel edge))
      ρ target).2 ⟨input.update.eval ρ, ⟨hguard, rfl⟩,
        ⟨hlabel.1, hlabel.2⟩⟩
    let successor : SymbolicSuccessor E Γinput Γ := {
      edge := edge
      step := input.compose
        (QFAbvStep.ofSymbolicLabel (model.edgeSemantics.symbolicLabel edge))
    }
    exact ⟨successor, ⟨edge, member, rfl⟩, rfl, hcomposed⟩

/-- Packaging a symbolic step as an STS preserves its exact source transition,
including the original edge label and the input guard/update semantics. -/
theorem ofSymbolicSuccessors_symbolicStep_transition_iff {Γ : Ctx} {E : Type}
    (model : SymbolicTransitionSystem Unit Γ E) (input : QFAbvStep Γ Γ)
    (source : Env Γ) (edge : E) (target : Env Γ) :
    (∃ successor,
      (ofSymbolicSuccessors (model.symbolicStep input)).toLTS.Tr
        ⟨(), source⟩ successor ⟨(), target⟩ ∧ successor.edge = edge) ↔
      Eval.evalBool source input.guard = true ∧
        model.toLTS.Tr ⟨(), input.update.eval source⟩ edge ⟨(), target⟩ := by
  rw [← symbolicStep_denotes_iff model input source edge target]
  constructor
  · rintro ⟨successor, transition, edgeEq⟩
    obtain ⟨member, denotes⟩ :=
      (ofSymbolicSuccessors_transition_iff _ _ _ _).1 transition
    exact ⟨successor, member, edgeEq, denotes⟩
  · rintro ⟨successor, member, edgeEq, denotes⟩
    exact ⟨successor,
      (ofSymbolicSuccessors_transition_iff _ _ _ _).2 ⟨member, denotes⟩, edgeEq⟩

/-- Every admitted returned successor denotes its own exact source edge. -/
theorem symbolicStep_sound {Γinput Γ : Ctx} {E : Type}
    (model : SymbolicTransitionSystem Unit Γ E)
    (input : QFAbvStep Γinput Γ) (successor : SymbolicSuccessor E Γinput Γ)
    (member : successor ∈ model.symbolicStep input) (ρ : Env Γinput)
    (admitted : Eval.evalBool ρ successor.step.guard = true) :
    Eval.evalBool ρ input.guard = true ∧
      model.toLTS.Tr ⟨(), input.update.eval ρ⟩ successor.edge
        ⟨(), successor.step.update.eval ρ⟩ := by
  obtain ⟨hguard, hstep⟩ :=
    (symbolicStep_denotes_iff model input ρ successor.edge
      (successor.step.update.eval ρ)).1
      ⟨successor, member, rfl, ⟨admitted, rfl⟩⟩
  exact ⟨hguard, hstep⟩

/-- Every source-indexed edge from an admitted represented state is returned
with the same edge label and its exact concrete target. -/
theorem symbolicStep_complete {Γinput Γ : Ctx} {E : Type}
    (model : SymbolicTransitionSystem Unit Γ E)
    (input : QFAbvStep Γinput Γ) (ρ : Env Γinput) (edge : E)
    (target : Env Γ)
    (admitted : Eval.evalBool ρ input.guard = true)
    (transition : model.toLTS.Tr ⟨(), input.update.eval ρ⟩ edge ⟨(), target⟩) :
    ∃ successor ∈ model.symbolicStep input,
      successor.edge = edge ∧ successor.step.denotes ρ target :=
  (symbolicStep_denotes_iff model input ρ edge target).2
    ⟨admitted, transition⟩

omit [FPInterpretation] in
/-- Enumeration preserves edge count, including duplicate or infeasible edges. -/
theorem symbolicStep_length {Γinput Γ : Ctx} {E : Type}
    (model : SymbolicTransitionSystem Unit Γ E)
    (input : QFAbvStep Γinput Γ) :
    (model.symbolicStep input).length = (model.transAt ()).length := by
  simp only [symbolicStep, ShareCommon.shareCommon', List.length_map]

end Ayxg.LTS.QfAbv.SymbolicTransitionSystem
