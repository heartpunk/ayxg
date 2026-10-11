import Ayxg.LTS.QfAbv.WholeStateRegionAlgebra
import Ayxg.QfAbv.SymbolicStep

namespace Ayxg.QfAbv.QFAbvSTS

variable [FPInterpretation]

open _root_.Ayxg.LTS.QfAbv

/-- The algebra's predecessor region is exact for the original whole-state STS. -/
theorem regionPre_iff {Γ : Ctx} (model : QFAbvSTS Γ)
    (observables : Region.Observables Unit Γ) (target : Region Unit Γ)
    (source : Env Γ) :
    ((model.toRegionAlgebra observables).pre target).Holds ⟨(), source⟩ ↔
      ∃ result : Env Γ,
        model.toLTS.canStep source result ∧ target.Holds ⟨(), result⟩ := by
  have hpre := RegionAlgebra.holds_pre_iff
    (model.toRegionAlgebra observables) target ⟨(), source⟩
  constructor
  · intro h
    obtain ⟨edge, successor, hstep, htarget⟩ := hpre.mp h
    cases successor with
    | mk control result =>
      cases control
      refine ⟨result, ?_, htarget⟩
      exact (model.toControlSystem_canStep_iff source result).mpr
        ⟨edge, by simpa [toRegionAlgebra, RegionAlgebra.ofFiniteControls] using hstep⟩
  · rintro ⟨result, hstep, htarget⟩
    obtain ⟨edge, hedge⟩ := (model.toControlSystem_canStep_iff source result).mp hstep
    apply hpre.mpr
    exact ⟨edge, ⟨(), result⟩,
      by simpa [toRegionAlgebra, RegionAlgebra.ofFiniteControls] using hedge,
      htarget⟩

/-- A Voogd-style symbolic successor reaches a region exactly when its
represented source state is in that region's one-step predecessor. -/
theorem symbolicStep_hits_region_iff {Γinput Γ : Ctx} (model : QFAbvSTS Γ)
    (observables : Region.Observables Unit Γ)
    (input : QFAbvStep Γinput Γ) (ρ : Env Γinput)
    (target : Region Unit Γ) :
    (∃ successor ∈ model.symbolicStep input,
      ∃ result : Env Γ,
        successor.denotes ρ result ∧ target.Holds ⟨(), result⟩) ↔
      Eval.evalBool ρ input.guard = true ∧
        ((model.toRegionAlgebra observables).pre target).Holds
          ⟨(), input.update.eval ρ⟩ := by
  constructor
  · rintro ⟨successor, hmember, result, hdenotes, htarget⟩
    obtain ⟨hguard, hstep⟩ :=
      (model.symbolicStep_denotes_iff input ρ result).mp
        ⟨successor, hmember, hdenotes⟩
    exact ⟨hguard, (model.regionPre_iff observables target _).mpr
      ⟨result, hstep, htarget⟩⟩
  · rintro ⟨hguard, hpre⟩
    obtain ⟨result, hstep, htarget⟩ :=
      (model.regionPre_iff observables target _).mp hpre
    obtain ⟨successor, hmember, hdenotes⟩ :=
      (model.symbolicStep_denotes_iff input ρ result).mpr ⟨hguard, hstep⟩
    exact ⟨successor, hmember, result, hdenotes, htarget⟩

end Ayxg.QfAbv.QFAbvSTS
