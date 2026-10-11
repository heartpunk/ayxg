import Ayxg.LTS.QfAbv.SymbolicTransitionSystem

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

/-- A QF_ABV region assigns a Boolean formula to each existing control site. -/
structure Region (C : Type) (Γ : Ctx) where
  formulaAt : C → Expr Γ .bool

namespace Region

/-- The subset of existing configurations denoted by a region. -/
def Holds [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (region : Region C Γ)
    (cfg : Config C Γ) : Prop :=
  Eval.evalBool cfg.env (region.formulaAt cfg.control) = true

/-- Intersection of regions, computed at each existing control site. -/
def inter {C : Type} {Γ : Ctx}
    (left right : Region C Γ) : Region C Γ where
  formulaAt := fun c => .boolAnd (left.formulaAt c) (right.formulaAt c)

/-- Region difference, computed at each existing control site. -/
def diff {C : Type} {Γ : Ctx}
    (left right : Region C Γ) : Region C Γ where
  formulaAt := fun c => .boolAnd (left.formulaAt c) (.boolNot (right.formulaAt c))

@[simp] theorem holds_inter_iff [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (left right : Region C Γ)
    (cfg : Config C Γ) :
    (left.inter right).Holds cfg ↔ left.Holds cfg ∧ right.Holds cfg := by
  simp [Holds, inter, Eval.evalBool, Eval.eval]

@[simp] theorem holds_diff_iff [_root_.Ayxg.QfAbv.FPInterpretation]
    {C : Type} {Γ : Ctx} (left right : Region C Γ)
    (cfg : Config C Γ) :
    (left.diff right).Holds cfg ↔ left.Holds cfg ∧ ¬ right.Holds cfg := by
  simp [Holds, diff, Eval.evalBool, Eval.eval]

end Region

end QfAbv
end LTS
end Ayxg
