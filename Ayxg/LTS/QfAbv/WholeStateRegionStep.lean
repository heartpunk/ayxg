import Ayxg.LTS.QfAbv.WholeStateRegionAlgebra
import Ayxg.LTS.QfAbv.SymbolicStep

namespace Ayxg.LTS.QfAbv

open _root_.Ayxg.QfAbv

variable [FPInterpretation]

/-- The algebra's predecessor formula is exact for the system's labeled
transitions between complete environments. -/
theorem wholeStateRegionPre_iff {Γ : Ctx}
    (system : SymbolicTransitionSystem Unit Γ (SymbolicTransition Unit Γ))
    (canonical : system.edgeSemantics = SymbolicTransition.edgeSemantics)
    (observables : Region.Observables Unit Γ) (target : Region Unit Γ)
    (source : Env Γ) :
    ((wholeStateRegionAlgebra system canonical observables).pre target).Holds
        ⟨(), source⟩ ↔
      ∃ (edge : SymbolicTransition Unit Γ) (result : Env Γ),
        system.toLTS.Tr ⟨(), source⟩ edge ⟨(), result⟩ ∧
        target.Holds ⟨(), result⟩ := by
  have hpre := RegionAlgebra.holds_pre_iff
    (wholeStateRegionAlgebra system canonical observables) target ⟨(), source⟩
  constructor
  · intro h
    obtain ⟨edge, successor, hstep, htarget⟩ := hpre.mp h
    cases successor with
    | mk control env =>
      cases control
      exact ⟨edge, env, hstep, htarget⟩
  · rintro ⟨edge, result, hstep, htarget⟩
    exact hpre.mpr ⟨edge, ⟨(), result⟩, hstep, htarget⟩

/-- A symbolic successor reaches a target region exactly when its retained
source edge labels a transition into that region. -/
theorem symbolicStepHitsRegion_iff {Γinput Γ : Ctx}
    (system : SymbolicTransitionSystem Unit Γ (SymbolicTransition Unit Γ))
    (canonical : system.edgeSemantics = SymbolicTransition.edgeSemantics)
    (observables : Region.Observables Unit Γ)
    (input : QFAbvStep Γinput Γ) (ρ : Env Γinput)
    (target : Region Unit Γ) :
    (∃ successor ∈ system.symbolicStep input,
      ∃ (edge : SymbolicTransition Unit Γ) (result : Env Γ),
        successor.edge = edge ∧
        system.toLTS.Tr ⟨(), input.update.eval ρ⟩ edge ⟨(), result⟩ ∧
        successor.step.denotes ρ result ∧
        target.Holds ⟨(), result⟩) ↔
      Eval.evalBool ρ input.guard = true ∧
        ((wholeStateRegionAlgebra system canonical observables).pre target).Holds
          ⟨(), input.update.eval ρ⟩ := by
  constructor
  · rintro ⟨successor, member, edge, result, edgeEq, transition,
      successorDenotes, targetHolds⟩
    obtain ⟨inputGuard, _⟩ :=
      (SymbolicTransitionSystem.symbolicStep_denotes_iff
        system input ρ edge result).1
        ⟨successor, member, edgeEq, successorDenotes⟩
    exact ⟨inputGuard,
      (wholeStateRegionPre_iff system canonical observables target _).mpr
        ⟨edge, result, transition, targetHolds⟩⟩
  · rintro ⟨inputGuard, pre⟩
    obtain ⟨edge, result, transition, targetHolds⟩ :=
      (wholeStateRegionPre_iff system canonical observables target _).mp pre
    obtain ⟨successor, member, edgeEq, successorDenotes⟩ :=
      (SymbolicTransitionSystem.symbolicStep_denotes_iff
        system input ρ edge result).2 ⟨inputGuard, transition⟩
    exact ⟨successor, member, edge, result, edgeEq, transition,
      successorDenotes, targetHolds⟩

end Ayxg.LTS.QfAbv
