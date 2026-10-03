import Ayxg.QfAbv.Update

namespace Ayxg
namespace QfAbv

variable [_root_.Ayxg.QfAbv.FPInterpretation]

/-- Symbolic guard/update payload over a QF_ABV environment.

This is the payload language used by the current QF_ABV LTS bridge: the guard
and every update right-hand side are expressions over the old context `Γ`, and
the update produces a fresh environment over the same context. It has no control
component by itself. -/
structure SymbolicLabel (Γ : Ctx) where
  guard : Expr Γ .bool
  update : StateUpdate Γ Γ

namespace SymbolicLabel

/-- The canonical identity label: an always-enabled identity update. -/
def identity (Γ : Ctx) : SymbolicLabel Γ where
  guard := Expr.boolLit true
  update := StateUpdate.identity Γ

/-- Relational meaning of a guard/update label between old and new
environments. -/
def denotes {Γ : Ctx} (l : SymbolicLabel Γ) (s t : Env Γ) : Prop :=
  Eval.evalBool s l.guard = true ∧ l.update.eval s = t

/-- The identity label denotes exactly an unchanged environment. -/
theorem identity_denotes_iff {Γ : Ctx} (s t : Env Γ) :
    (identity Γ).denotes s t ↔ s = t := by
  simp [identity, denotes, Eval.evalBool, Eval.eval, StateUpdate.eval_identity]

/-- Sequentially compose symbolic labels using ICTAC-style guard lifting:
`(φ₁, σ₁) ; (φ₂, σ₂) = (φ₁ ∧ σ₁(φ₂), σ₁ ; σ₂)`. -/
def compose {Γ : Ctx} (left right : SymbolicLabel Γ) : SymbolicLabel Γ :=
  { guard := Expr.boolAnd left.guard (Expr.subst left.update.toSubst right.guard)
    update := left.update.compose right.update }

/-- Semantic correctness of symbolic label composition. -/
theorem compose_denotes_iff {Γ : Ctx} (left right : SymbolicLabel Γ)
    (s t : Env Γ) :
    (left.compose right).denotes s t ↔
      ∃ mid, left.denotes s mid ∧ right.denotes mid t := by
  constructor
  · intro h
    rcases h with ⟨hguard, hupdate⟩
    dsimp [compose, denotes] at hguard hupdate ⊢
    simp [Eval.eval] at hguard
    rcases hguard with ⟨hleftGuard, hrightGuard⟩
    exists left.update.eval s
    constructor
    · exact ⟨hleftGuard, rfl⟩
    · constructor
      · rw [Expr.eval_subst left.update.toSubst s right.guard] at hrightGuard
        rw [StateUpdate.eval_eq_subst_eval left.update s] at hrightGuard
        exact hrightGuard
      · rw [StateUpdate.eval_compose left.update right.update s] at hupdate
        exact hupdate
  · intro h
    rcases h with ⟨mid, ⟨hleftGuard, hleftUpdate⟩, ⟨hrightGuard, hrightUpdate⟩⟩
    dsimp [denotes] at hleftGuard hleftUpdate hrightGuard hrightUpdate
    subst mid
    dsimp [compose, denotes]
    constructor
    · simp [Eval.eval, hleftGuard]
      rw [Expr.eval_subst left.update.toSubst s right.guard]
      rw [StateUpdate.eval_eq_subst_eval left.update s]
      exact hrightGuard
    · rw [StateUpdate.eval_compose left.update right.update s]
      exact hrightUpdate

/-- Left composition by the identity label is relationally neutral. -/
theorem identity_compose_denotes_iff {Γ : Ctx} (label : SymbolicLabel Γ)
    (s t : Env Γ) :
    ((identity Γ).compose label).denotes s t ↔ label.denotes s t := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨mid, hIdentity, hLabel⟩
    rw [identity_denotes_iff] at hIdentity
    subst mid
    exact hLabel
  · intro hLabel
    exact ⟨s, (identity_denotes_iff s s).2 rfl, hLabel⟩

/-- Right composition by the identity label is relationally neutral. -/
theorem compose_identity_denotes_iff {Γ : Ctx} (label : SymbolicLabel Γ)
    (s t : Env Γ) :
    (label.compose (identity Γ)).denotes s t ↔ label.denotes s t := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨mid, hLabel, hIdentity⟩
    rw [identity_denotes_iff] at hIdentity
    subst t
    exact hLabel
  · intro hLabel
    exact ⟨t, hLabel, (identity_denotes_iff t t).2 rfl⟩

/-- Compose a nonempty finite path of symbolic labels.

The singleton path denotes the head label itself. Longer paths use binary
`SymbolicLabel.compose`. There is deliberately no empty case; callers that need
a zero-step summary use `SymbolicLabel.identity` explicitly. -/
def composeNonempty {Γ : Ctx} (head : SymbolicLabel Γ) :
    List (SymbolicLabel Γ) → SymbolicLabel Γ
  | [] => head
  | next :: rest => head.compose (composeNonempty next rest)

/-- Relational meaning of a nonempty finite path of symbolic labels. -/
inductive DenotesNonempty {Γ : Ctx} :
    SymbolicLabel Γ → List (SymbolicLabel Γ) → Env Γ → Env Γ → Prop where
  | single : head.denotes s t → DenotesNonempty head [] s t
  | cons : head.denotes s mid → DenotesNonempty next rest mid t →
      DenotesNonempty head (next :: rest) s t

/-- Nonempty symbolic-label composition denotes exactly sequential execution
through the head label and every label in the tail. -/
theorem denotes_composeNonempty_iff {Γ : Ctx}
    (head : SymbolicLabel Γ) (tail : List (SymbolicLabel Γ)) (s t : Env Γ) :
    (composeNonempty head tail).denotes s t ↔ DenotesNonempty head tail s t := by
  induction tail generalizing head s with
  | nil =>
      constructor
      · intro h
        exact DenotesNonempty.single h
      · intro h
        cases h with
        | single hden => exact hden
  | cons next rest ih =>
      dsimp [composeNonempty]
      rw [SymbolicLabel.compose_denotes_iff]
      constructor
      · rintro ⟨mid, hHead, hTail⟩
        exact DenotesNonempty.cons hHead ((ih next mid).1 hTail)
      · intro h
        cases h with
        | cons hHead hTail =>
            exact ⟨_, hHead, (ih next _).2 hTail⟩

end SymbolicLabel

end QfAbv
end Ayxg
