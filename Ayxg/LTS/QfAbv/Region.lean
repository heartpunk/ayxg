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

/-- Pull a target region back through one existing guarded-update edge. -/
def preEdge {C : Type} [DecidableEq C] {Γ : Ctx}
    (edge : SymbolicTransition C Γ) (target : Region C Γ) : Region C Γ where
  formulaAt := fun c =>
    if edge.src = c then
      .boolAnd edge.label.guard
        (Expr.subst edge.label.update.toSubst
          (target.formulaAt (edge.tgt.getD c)))
    else .boolLit false

/-- The formula for one edge describes exactly its enabled predecessors. -/
theorem holds_preEdge_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx} (edge : SymbolicTransition C Γ)
    (target : Region C Γ) (source : Config C Γ) :
    (preEdge edge target).Holds source ↔
      edge.src = source.control ∧
      Eval.evalBool source.env edge.label.guard = true ∧
      target.Holds (edge.nextConfig source) := by
  by_cases hsrc : edge.src = source.control
  · simp [Holds, preEdge, hsrc, SymbolicTransition.nextConfig,
      Eval.evalBool, Eval.eval, Expr.eval_subst,
      StateUpdate.eval_eq_subst_eval]
  · simp [Holds, preEdge, hsrc, Eval.evalBool, Eval.eval]

/-- A configuration is in the one-edge predecessor exactly when the edge can
reach a configuration in the target region. -/
theorem holds_preEdge_exists_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx} (edge : SymbolicTransition C Γ)
    (target : Region C Γ) (source : Config C Γ) :
    (preEdge edge target).Holds source ↔
      ∃ successor, edge.denotes source successor ∧ target.Holds successor := by
  rw [holds_preEdge_iff]
  constructor
  · rintro ⟨hsrc, hguard, htarget⟩
    exact ⟨edge.nextConfig source, ⟨hsrc, hguard, rfl⟩, htarget⟩
  · rintro ⟨successor, ⟨hsrc, hguard, hnext⟩, htarget⟩
    rw [← hnext] at htarget
    exact ⟨hsrc, hguard, htarget⟩

end Region

end QfAbv
end LTS
end Ayxg
