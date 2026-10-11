import Ayxg.QfAbv.STS
import Ayxg.LTS.QfAbv.SymbolicTransitionSystem

namespace Ayxg.QfAbv.QFAbvSTS

variable [FPInterpretation]

/-- Give a whole-state QF_ABV step the sole structural control site. -/
def toControlEdge {Γ : Ctx} (step : QFAbvStep Γ Γ) :
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition Unit Γ where
  src := ()
  tgt := none
  label := { guard := step.guard, update := step.update }

/-- The finite whole-state rule list, viewed as source-indexed edges. -/
def toControlSystem {Γ : Ctx} (model : QFAbvSTS Γ) :
    _root_.Ayxg.LTS.QfAbv.SymbolicTransitionSystem Unit Γ
      (_root_.Ayxg.LTS.QfAbv.SymbolicTransition Unit Γ) :=
  _root_.Ayxg.LTS.QfAbv.SymbolicTransitionSystem.legacy
    (fun _ => model.steps.map toControlEdge)

private theorem toControlEdge_injective {Γ : Ctx} :
    Function.Injective (toControlEdge (Γ := Γ)) := by
  intro a b h
  cases a with
  | mk agu aup =>
    cases b with
    | mk bgu bup =>
      cases h
      rfl

/-- A converted edge occurs precisely when its original step occurs. -/
theorem toControlEdge_mem_iff {Γ : Ctx} (model : QFAbvSTS Γ)
    (step : QFAbvStep Γ Γ) :
    toControlEdge step ∈ (model.toControlSystem).transAt () ↔
      step ∈ model.steps := by
  change toControlEdge step ∈ model.steps.map toControlEdge ↔ step ∈ model.steps
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
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition.denotes (toControlEdge step)
      ⟨(), source⟩ ⟨(), target⟩ ↔ step.denotes source target := by
  simp [QFAbvStep.denotes, _root_.Ayxg.LTS.QfAbv.SymbolicTransition.denotes,
    _root_.Ayxg.LTS.QfAbv.SymbolicEdgeSemantics.denotes,
    _root_.Ayxg.LTS.QfAbv.SymbolicEdgeSemantics.nextConfig,
    _root_.Ayxg.LTS.QfAbv.SymbolicTransition.edgeSemantics,
    toControlEdge]

/-- Exact labeled one-step correspondence for the finite model and its graph view. -/
theorem toControlSystem_step_iff {Γ : Ctx} (model : QFAbvSTS Γ)
    (step : QFAbvStep Γ Γ) (source target : Env Γ) :
    model.toLTS.Tr source step target ↔
      model.toControlSystem.toLTS.Tr ⟨(), source⟩ (toControlEdge step)
        ⟨(), target⟩ := by
  change (step ∈ model.steps ∧ step.denotes source target) ↔
    (toControlEdge step ∈ (model.toControlSystem).transAt () ∧
      _root_.Ayxg.LTS.QfAbv.SymbolicTransition.denotes (toControlEdge step)
        ⟨(), source⟩ ⟨(), target⟩)
  rw [toControlEdge_mem_iff, toControlEdge_denotes_iff]

/-- Exact unlabeled one-step correspondence: no converted edge invents a move. -/
theorem toControlSystem_canStep_iff {Γ : Ctx} (model : QFAbvSTS Γ)
    (source target : Env Γ) :
    model.toLTS.canStep source target ↔
      model.toControlSystem.toLTS.canStep ⟨(), source⟩ ⟨(), target⟩ := by
  constructor
  · rintro ⟨step, hstep⟩
    exact ⟨toControlEdge step, (toControlSystem_step_iff model step source target).mp hstep⟩
  · rintro ⟨edge, hstep⟩
    obtain ⟨step, hmem, heq⟩ := List.mem_map.mp hstep.1
    subst edge
    exact ⟨step, (toControlSystem_step_iff model step source target).mpr hstep⟩

end Ayxg.QfAbv.QFAbvSTS
