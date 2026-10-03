import Ayxg.QfAbv.STS
import Init.ShareCommon

namespace Ayxg.QfAbv.QFAbvSTS

/-- Voogd stepping: each source edge extends the input substitution/path condition.
No satisfiability pruning occurs. The existing composition performs guard pullback
and simultaneous substitution. Lean's standard value-preserving hash-consing
primitive shares common subexpressions across the complete returned family. -/
def symbolicStep {Γinput Γ : Ctx} (model : QFAbvSTS Γ)
    (input : QFAbvStep Γinput Γ) : List (QFAbvStep Γinput Γ) :=
  ShareCommon.shareCommon' (model.steps.map (input.compose ·))

variable [FPInterpretation]

/-- Exact connection to the SOURCE STS's concrete transition relation, under the
same initial valuation on both input and successor symbolic states. No extraction
result, supplied transcript, or assumed correspondence occurs in the premises. -/
theorem symbolicStep_denotes_iff {Γinput Γ : Ctx} (model : QFAbvSTS Γ)
    (input : QFAbvStep Γinput Γ) (ρ : Env Γinput) (target : Env Γ) :
    (∃ successor ∈ model.symbolicStep input, successor.denotes ρ target) ↔
      Eval.evalBool ρ input.guard = true ∧
        model.toLTS.canStep (input.update.eval ρ) target := by
  simp only [symbolicStep, ShareCommon.shareCommon', List.mem_map]
  constructor
  · rintro ⟨successor, ⟨edge, member, rfl⟩, transition⟩
    obtain ⟨middle, hinput, hedge⟩ :=
      (QFAbvStep.compose_denotes_iff input edge ρ target).1 transition
    rcases hinput with ⟨hguard, hupdate⟩
    subst middle
    exact ⟨hguard, edge, member, hedge⟩
  · rintro ⟨hguard, edge, member, hedge⟩
    refine ⟨input.compose edge, ⟨edge, member, rfl⟩, ?_⟩
    exact (QFAbvStep.compose_denotes_iff input edge ρ target).2
      ⟨input.update.eval ρ, ⟨hguard, rfl⟩, hedge⟩

/-- Every admitted returned successor performs an actual source-STS step and
preserves admission of the input symbolic state. -/
theorem symbolicStep_sound {Γinput Γ : Ctx} (model : QFAbvSTS Γ)
    (input successor : QFAbvStep Γinput Γ)
    (member : successor ∈ model.symbolicStep input) (ρ : Env Γinput)
    (admitted : Eval.evalBool ρ successor.guard = true) :
    Eval.evalBool ρ input.guard = true ∧
      model.toLTS.canStep (input.update.eval ρ) (successor.update.eval ρ) :=
  (symbolicStep_denotes_iff model input ρ (successor.update.eval ρ)).1
    ⟨successor, member, admitted, rfl⟩

/-- Every source-STS step from an admitted represented state has a returned
symbolic successor realizing exactly that target under the same valuation. -/
theorem symbolicStep_complete {Γinput Γ : Ctx} (model : QFAbvSTS Γ)
    (input : QFAbvStep Γinput Γ) (ρ : Env Γinput) (target : Env Γ)
    (admitted : Eval.evalBool ρ input.guard = true)
    (transition : model.toLTS.canStep (input.update.eval ρ) target) :
    ∃ successor ∈ model.symbolicStep input,
      Eval.evalBool ρ successor.guard = true ∧ successor.update.eval ρ = target :=
  (symbolicStep_denotes_iff model input ρ target).2 ⟨admitted, transition⟩

omit [FPInterpretation] in
/-- Enumeration preserves edge count, including duplicate or infeasible edges. -/
theorem symbolicStep_length {Γinput Γ : Ctx} (model : QFAbvSTS Γ)
    (input : QFAbvStep Γinput Γ) :
    (model.symbolicStep input).length = model.steps.length := by
  simp [symbolicStep, ShareCommon.shareCommon']

end Ayxg.QfAbv.QFAbvSTS
