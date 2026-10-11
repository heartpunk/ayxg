import Ayxg.LTS.QfAbv.Region

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

namespace Region

/-- The complement of a region, computed at every existing control site. -/
def compl {C : Type} {Γ : Ctx} (region : Region C Γ) : Region C Γ where
  formulaAt := fun c => .boolNot (region.formulaAt c)

@[simp] theorem holds_compl_iff [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (region : Region C Γ) (cfg : Config C Γ) :
    (compl region).Holds cfg ↔ ¬ region.Holds cfg := by
  simp [Holds, compl, Eval.evalBool, Eval.eval]

/-- The region containing every existing configuration. -/
def univ {C : Type} {Γ : Ctx} : Region C Γ where
  formulaAt := fun _ => .boolLit true

@[simp] theorem holds_univ [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (cfg : Config C Γ) :
    (univ : Region C Γ).Holds cfg := by
  simp [Holds, univ, Eval.evalBool, Eval.eval]

/-- Henzinger–Majumdar–Raskin observables over the existing configurations:
a finite family of regions that covers the states and contains a denotational
complement for each of its members. -/
structure Observables (C : Type) (Γ : Ctx)
    [_root_.Ayxg.QfAbv.FPInterpretation] where
  regions : List (Region C Γ)
  covers : ∀ cfg : Config C Γ,
    ∃ region, region ∈ regions ∧ region.Holds cfg
  complementClosed : ∀ region ∈ regions,
    ∃ complement ∈ regions,
      ∀ cfg : Config C Γ, complement.Holds cfg ↔ ¬ region.Holds cfg

end Region

end QfAbv
end LTS
end Ayxg
