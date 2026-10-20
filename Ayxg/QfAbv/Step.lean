import Ayxg.STS
import Ayxg.QfAbv.SymbolicLabel

namespace Ayxg.QfAbv

variable [FPInterpretation]

/-- Heterogeneous guarded state transformer, also used for segment adapters. -/
structure QFAbvStep (Γin Γout : Ctx) where
  guard : Expr Γin .bool
  update : StateUpdate Γin Γout

namespace QFAbvStep

def denotes {Γin Γout : Ctx} (step : QFAbvStep Γin Γout)
    (source : Env Γin) (target : Env Γout) : Prop :=
  Eval.evalBool source step.guard = true ∧ step.update.eval source = target

def identity (Γ : Ctx) : QFAbvStep Γ Γ where
  guard := .boolLit true
  update := StateUpdate.identity Γ

/-- Sequencing lifts the right guard through the left simultaneous update. -/
def compose {Γ₀ Γ₁ Γ₂ : Ctx} (left : QFAbvStep Γ₀ Γ₁)
    (right : QFAbvStep Γ₁ Γ₂) : QFAbvStep Γ₀ Γ₂ where
  guard := .boolAnd left.guard (Expr.subst left.update.toSubst right.guard)
  update := left.update.compose right.update

/-- Existing homogeneous symbolic labels embed without changing their meaning. -/
def ofSymbolicLabel {Γ : Ctx} (label : SymbolicLabel Γ) : QFAbvStep Γ Γ where
  guard := label.guard
  update := label.update

/-- Law statement: sequencing denotes relational composition. -/
def compositionDenotationLaw : Prop :=
  ∀ {Γ₀ Γ₁ Γ₂ : Ctx} (left : QFAbvStep Γ₀ Γ₁) (right : QFAbvStep Γ₁ Γ₂)
    (source : Env Γ₀) (target : Env Γ₂),
    (left.compose right).denotes source target ↔
      ∃ middle, left.denotes source middle ∧ right.denotes middle target

/-- Law statement: the identity step denotes equality of full states. -/
def identityDenotationLaw : Prop :=
  ∀ {Γ : Ctx} (source target : Env Γ),
    (identity Γ).denotes source target ↔ source = target

/-- Law statement: associativity is semantic, without requiring AST equality. -/
def associativityDenotationLaw : Prop :=
  ∀ {Γ₀ Γ₁ Γ₂ Γ₃ : Ctx}
    (a : QFAbvStep Γ₀ Γ₁) (b : QFAbvStep Γ₁ Γ₂) (c : QFAbvStep Γ₂ Γ₃)
    (source : Env Γ₀) (target : Env Γ₃),
    ((a.compose b).compose c).denotes source target ↔
      (a.compose (b.compose c)).denotes source target

/-- Guard lifting and simultaneous substitution preserve heterogeneous sequencing. -/
theorem compose_denotes_iff {Γ₀ Γ₁ Γ₂ : Ctx}
    (left : QFAbvStep Γ₀ Γ₁) (right : QFAbvStep Γ₁ Γ₂)
    (source : Env Γ₀) (target : Env Γ₂) :
    (left.compose right).denotes source target ↔
      ∃ middle, left.denotes source middle ∧ right.denotes middle target := by
  constructor
  · rintro ⟨hguard, hupdate⟩
    dsimp [compose, denotes] at hguard hupdate ⊢
    simp [Eval.eval] at hguard
    rcases hguard with ⟨hleft, hright⟩
    refine ⟨left.update.eval source, ⟨hleft, rfl⟩, ?_, ?_⟩
    · rw [Expr.eval_subst left.update.toSubst source right.guard,
          StateUpdate.eval_eq_subst_eval left.update source] at hright
      exact hright
    · rw [StateUpdate.eval_compose left.update right.update source] at hupdate
      exact hupdate
  · rintro ⟨middle, ⟨hleft, hleftUpdate⟩, ⟨hright, hrightUpdate⟩⟩
    dsimp [denotes] at hleft hleftUpdate hright hrightUpdate
    subst middle
    dsimp [compose, denotes]
    constructor
    · simp [Eval.eval, hleft]
      rw [Expr.eval_subst left.update.toSubst source right.guard,
          StateUpdate.eval_eq_subst_eval left.update source]
      exact hright
    · rw [StateUpdate.eval_compose left.update right.update source]
      exact hrightUpdate

theorem compositionDenotationLaw_holds : compositionDenotationLaw := by
  intro Γ₀ Γ₁ Γ₂ left right source target
  exact compose_denotes_iff left right source target

/-- Identity preserves the entire environment, including implementation control. -/
theorem identity_denotes_iff {Γ : Ctx} (source target : Env Γ) :
    (identity Γ).denotes source target ↔ source = target := by
  simp [identity, denotes, Eval.evalBool, Eval.eval, StateUpdate.eval_identity]

theorem identityDenotationLaw_holds : identityDenotationLaw := by
  intro Γ source target
  exact identity_denotes_iff source target

theorem identity_compose_denotes_iff {Γ₀ Γ₁ : Ctx}
    (step : QFAbvStep Γ₀ Γ₁) (source : Env Γ₀) (target : Env Γ₁) :
    ((identity Γ₀).compose step).denotes source target ↔ step.denotes source target := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨middle, hidentity, hstep⟩
    rw [identity_denotes_iff] at hidentity
    subst middle
    exact hstep
  · intro hstep
    exact ⟨source, (identity_denotes_iff source source).2 rfl, hstep⟩

theorem compose_identity_denotes_iff {Γ₀ Γ₁ : Ctx}
    (step : QFAbvStep Γ₀ Γ₁) (source : Env Γ₀) (target : Env Γ₁) :
    (step.compose (identity Γ₁)).denotes source target ↔ step.denotes source target := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨middle, hstep, hidentity⟩
    rw [identity_denotes_iff] at hidentity
    subst target
    exact hstep
  · intro hstep
    exact ⟨target, hstep, (identity_denotes_iff target target).2 rfl⟩

/-- Associativity concerns relational denotation, not expression-tree shape. -/
theorem compose_assoc_denotes_iff {Γ₀ Γ₁ Γ₂ Γ₃ : Ctx}
    (a : QFAbvStep Γ₀ Γ₁) (b : QFAbvStep Γ₁ Γ₂) (c : QFAbvStep Γ₂ Γ₃)
    (source : Env Γ₀) (target : Env Γ₃) :
    ((a.compose b).compose c).denotes source target ↔
      (a.compose (b.compose c)).denotes source target := by
  simp only [compose_denotes_iff]
  constructor
  · rintro ⟨middle₂, ⟨middle₁, ha, hb⟩, hc⟩
    exact ⟨middle₁, ha, middle₂, hb, hc⟩
  · rintro ⟨middle₁, ha, middle₂, hb, hc⟩
    exact ⟨middle₂, ⟨middle₁, ha, hb⟩, hc⟩

theorem associativityDenotationLaw_holds : associativityDenotationLaw := by
  intro Γ₀ Γ₁ Γ₂ Γ₃ a b c source target
  exact compose_assoc_denotes_iff a b c source target

end QFAbvStep

abbrev QFAbvAdapter (Γin Γout : Ctx) :=
  Ayxg.Adapter (Env Γin) (Env Γout) (QFAbvStep Γin Γout)

abbrev QFAbvSegment (Γin Γbody Γout : Ctx) :=
  Ayxg.Segment (Env Γin) (Env Γbody) (Env Γout)
    (QFAbvStep Γbody Γbody) (QFAbvStep Γin Γbody) (QFAbvStep Γbody Γout)

namespace QFAbvSegment

def denotes {Γin Γbody Γout : Ctx} (segment : QFAbvSegment Γin Γbody Γout)
    (source : Env Γin) (target : Env Γout) : Prop :=
  Ayxg.Segment.denotes segment
    (fun source step target => step.denotes source target)
    (fun source step target => step.denotes source target)
    (fun source step target => step.denotes source target) source target

end QFAbvSegment

/-- A control view is an ordinary typed expression over complete state. -/
abbrev QFAbvControlView (Γ : Ctx) (sort : TermSort) :=
  Ayxg.ControlView (Env Γ) (Denote sort) (Expr Γ sort)

namespace QFAbvControlView

def observe {Γ : Ctx} {sort : TermSort} (view : QFAbvControlView Γ sort)
    (state : Env Γ) : Denote sort :=
  Eval.eval state view.projection

end QFAbvControlView

end Ayxg.QfAbv
