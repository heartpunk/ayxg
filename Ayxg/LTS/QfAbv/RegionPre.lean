import Ayxg.LTS.QfAbv.Region

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

namespace Region

/-- Disjoin the one-edge predecessor formulas in an existing control site's
outgoing edge list. The model must use those edges' guarded-update semantics.
This adds no states or edges to the source graph. -/
def pre {C : Type} [DecidableEq C] {Γ : Ctx}
    (m : SymbolicTransitionSystem C Γ (SymbolicTransition C Γ))
    (_canonical : m.edgeSemantics = SymbolicTransition.edgeSemantics)
    (target : Region C Γ) : Region C Γ where
  formulaAt := fun c =>
    (m.transAt c).foldr
      (fun edge acc => .boolOr ((preEdge edge target).formulaAt c) acc)
      (.boolLit false)

private theorem eval_foldr_pre_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (edges : List (SymbolicTransition C Γ))
    (target : Region C Γ) (source : Config C Γ) :
    Eval.evalBool source.env
      (edges.foldr
        (fun edge acc => .boolOr ((preEdge edge target).formulaAt source.control) acc)
        (.boolLit false)) = true ↔
      ∃ edge ∈ edges, (preEdge edge target).Holds source := by
  induction edges with
  | nil =>
      simp [Eval.evalBool, Eval.eval]
  | cons edge rest ih =>
      simp only [List.foldr_cons]
      simp only [Eval.evalBool, Eval.eval]
      change
        ((Eval.evalBool source.env ((preEdge edge target).formulaAt source.control)) ||
          (Eval.evalBool source.env
            (rest.foldr
              (fun edge acc => .boolOr ((preEdge edge target).formulaAt source.control) acc)
              (.boolLit false)))) = true ↔
          ∃ witness ∈ edge :: rest, (preEdge witness target).Holds source
      simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp, ih, Holds]

/-- Exact one-step predecessor for the existing graph with its canonical
guarded-update edge semantics. -/
theorem holds_pre_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (m : SymbolicTransitionSystem C Γ (SymbolicTransition C Γ))
    (hsem : m.edgeSemantics = SymbolicTransition.edgeSemantics)
    (target : Region C Γ) (source : Config C Γ) :
    (pre m hsem target).Holds source ↔
      ∃ edge successor,
        m.toLTS.Tr source edge successor ∧ target.Holds successor := by
  rw [show (pre m hsem target).Holds source ↔
      ∃ edge ∈ m.transAt source.control, (preEdge edge target).Holds source from
      eval_foldr_pre_iff (m.transAt source.control) target source]
  simp only [holds_preEdge_exists_iff]
  constructor
  · rintro ⟨edge, hmem, successor, hdenotes, htarget⟩
    exact ⟨edge, successor, ⟨hmem, by simpa [SymbolicTransitionSystem.toLTS, hsem,
      SymbolicTransition.denotes] using hdenotes⟩, htarget⟩
  · rintro ⟨edge, successor, ⟨hmem, hdenotes⟩, htarget⟩
    exact ⟨edge, hmem, successor, by simpa [SymbolicTransitionSystem.toLTS, hsem,
      SymbolicTransition.denotes] using hdenotes, htarget⟩

end Region

end QfAbv
end LTS
end Ayxg
