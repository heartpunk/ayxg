import Ayxg.STS
import Ayxg.QfAbv.SymbolicLabel

namespace Ayxg.QfAbv

variable [FPInterpretation]

/-- A guarded transition within one QF_ABV state context. -/
structure QFAbvStep (Γ : Ctx) where
  guard : Expr Γ .bool
  update : StateUpdate Γ Γ

namespace QFAbvStep

def denotes {Γ : Ctx} (step : QFAbvStep Γ) (source target : Env Γ) : Prop :=
  Eval.evalBool source step.guard = true ∧ step.update.eval source = target

end QFAbvStep

/-- A guarded state transformer across QF_ABV contexts. Adapters are a
separate semantic role from in-system transitions, even when both contexts
happen to be equal. -/
structure QFAbvAdapter (Γin Γout : Ctx) where
  guard : Expr Γin .bool
  update : StateUpdate Γin Γout

namespace QFAbvAdapter

def denotes {Γin Γout : Ctx} (adapter : QFAbvAdapter Γin Γout)
    (source : Env Γin) (target : Env Γout) : Prop :=
  Eval.evalBool source adapter.guard = true ∧ adapter.update.eval source = target

/-- Identity glue between equal state contexts. -/
def identity (Γ : Ctx) : QFAbvAdapter Γ Γ where
  guard := .boolLit true
  update := StateUpdate.identity Γ

/-- Sequentially compose two adapters, lifting the second guard through the
first simultaneous update. -/
def compose {Γ₀ Γ₁ Γ₂ : Ctx} (left : QFAbvAdapter Γ₀ Γ₁)
    (right : QFAbvAdapter Γ₁ Γ₂) : QFAbvAdapter Γ₀ Γ₂ where
  guard := .boolAnd left.guard (Expr.subst left.update.toSubst right.guard)
  update := left.update.compose right.update

/-- Compose input glue with an in-system transition. -/
def composeStep {Γ₀ Γ₁ : Ctx} (left : QFAbvAdapter Γ₀ Γ₁)
    (right : QFAbvStep Γ₁) : QFAbvAdapter Γ₀ Γ₁ where
  guard := .boolAnd left.guard (Expr.subst left.update.toSubst right.guard)
  update := left.update.compose right.update

/-- Compose an in-system transition with output glue. -/
def stepCompose {Γ₀ Γ₁ : Ctx} (left : QFAbvStep Γ₀)
    (right : QFAbvAdapter Γ₀ Γ₁) : QFAbvAdapter Γ₀ Γ₁ where
  guard := .boolAnd left.guard (Expr.subst left.update.toSubst right.guard)
  update := left.update.compose right.update

theorem compose_denotes_iff {Γ₀ Γ₁ Γ₂ : Ctx}
    (left : QFAbvAdapter Γ₀ Γ₁) (right : QFAbvAdapter Γ₁ Γ₂)
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

theorem composeStep_denotes_iff {Γ₀ Γ₁ : Ctx}
    (left : QFAbvAdapter Γ₀ Γ₁) (right : QFAbvStep Γ₁)
    (source : Env Γ₀) (target : Env Γ₁) :
    (left.composeStep right).denotes source target ↔
      ∃ middle, left.denotes source middle ∧ right.denotes middle target := by
  cases right
  exact compose_denotes_iff left ⟨_, _⟩ source target

theorem stepCompose_denotes_iff {Γ₀ Γ₁ : Ctx}
    (left : QFAbvStep Γ₀) (right : QFAbvAdapter Γ₀ Γ₁)
    (source : Env Γ₀) (target : Env Γ₁) :
    (QFAbvAdapter.stepCompose left right).denotes source target ↔
      ∃ middle, left.denotes source middle ∧ right.denotes middle target := by
  cases left
  exact compose_denotes_iff ⟨_, _⟩ right source target

theorem identity_denotes_iff {Γ : Ctx} (source target : Env Γ) :
    (identity Γ).denotes source target ↔ source = target := by
  simp [identity, denotes, Eval.evalBool, Eval.eval, StateUpdate.eval_identity]

theorem identity_compose_denotes_iff {Γ₀ Γ₁ : Ctx}
    (adapter : QFAbvAdapter Γ₀ Γ₁) (source : Env Γ₀) (target : Env Γ₁) :
    ((identity Γ₀).compose adapter).denotes source target ↔
      adapter.denotes source target := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨middle, hid, ha⟩
    rw [identity_denotes_iff] at hid
    subst middle
    exact ha
  · intro ha
    exact ⟨source, (identity_denotes_iff source source).2 rfl, ha⟩

theorem compose_identity_denotes_iff {Γ₀ Γ₁ : Ctx}
    (adapter : QFAbvAdapter Γ₀ Γ₁) (source : Env Γ₀) (target : Env Γ₁) :
    (adapter.compose (identity Γ₁)).denotes source target ↔
      adapter.denotes source target := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨middle, ha, hid⟩
    rw [identity_denotes_iff] at hid
    subst target
    exact ha
  · intro ha
    exact ⟨target, ha, (identity_denotes_iff target target).2 rfl⟩

theorem compose_assoc_denotes_iff {Γ₀ Γ₁ Γ₂ Γ₃ : Ctx}
    (a : QFAbvAdapter Γ₀ Γ₁) (b : QFAbvAdapter Γ₁ Γ₂)
    (c : QFAbvAdapter Γ₂ Γ₃) (source : Env Γ₀) (target : Env Γ₃) :
    ((a.compose b).compose c).denotes source target ↔
      (a.compose (b.compose c)).denotes source target := by
  simp only [compose_denotes_iff]
  constructor
  · rintro ⟨middle₂, ⟨middle₁, ha, hb⟩, hc⟩
    exact ⟨middle₁, ha, middle₂, hb, hc⟩
  · rintro ⟨middle₁, ha, middle₂, hb, hc⟩
    exact ⟨middle₂, ⟨middle₁, ha, hb⟩, hc⟩

end QFAbvAdapter

namespace QFAbvStep

def identity (Γ : Ctx) : QFAbvStep Γ where
  guard := .boolLit true
  update := StateUpdate.identity Γ

/-- Homogeneous sequencing remains within the system context. -/
def compose {Γ : Ctx} (left right : QFAbvStep Γ) : QFAbvStep Γ where
  guard := .boolAnd left.guard (Expr.subst left.update.toSubst right.guard)
  update := left.update.compose right.update

def toAdapter {Γ : Ctx} (step : QFAbvStep Γ) : QFAbvAdapter Γ Γ :=
  ⟨step.guard, step.update⟩

def ofSymbolicLabel {Γ : Ctx} (label : SymbolicLabel Γ) : QFAbvStep Γ :=
  ⟨label.guard, label.update⟩

def compositionDenotationLaw : Prop :=
  ∀ {Γ : Ctx} (left right : QFAbvStep Γ) (source target : Env Γ),
    (left.compose right).denotes source target ↔
      ∃ middle, left.denotes source middle ∧ right.denotes middle target

def identityDenotationLaw : Prop :=
  ∀ {Γ : Ctx} (source target : Env Γ),
    (identity Γ).denotes source target ↔ source = target

def associativityDenotationLaw : Prop :=
  ∀ {Γ : Ctx} (a b c : QFAbvStep Γ) (source target : Env Γ),
    ((a.compose b).compose c).denotes source target ↔
      (a.compose (b.compose c)).denotes source target

theorem compose_denotes_iff {Γ : Ctx} (left right : QFAbvStep Γ)
    (source target : Env Γ) :
    (left.compose right).denotes source target ↔
      ∃ middle, left.denotes source middle ∧ right.denotes middle target := by
  simpa [compose, denotes, QFAbvAdapter.denotes, QFAbvAdapter.compose,
    QFAbvStep.toAdapter] using
    (QFAbvAdapter.compose_denotes_iff left.toAdapter right.toAdapter source target)

theorem identity_denotes_iff {Γ : Ctx} (source target : Env Γ) :
    (identity Γ).denotes source target ↔ source = target := by
  simp [identity, denotes, Eval.evalBool, Eval.eval, StateUpdate.eval_identity]

theorem identity_compose_denotes_iff {Γ : Ctx} (step : QFAbvStep Γ)
    (source target : Env Γ) :
    ((identity Γ).compose step).denotes source target ↔ step.denotes source target := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨middle, hid, hs⟩
    rw [identity_denotes_iff] at hid
    subst middle
    exact hs
  · intro hs
    exact ⟨source, (identity_denotes_iff source source).2 rfl, hs⟩

theorem compose_identity_denotes_iff {Γ : Ctx} (step : QFAbvStep Γ)
    (source target : Env Γ) :
    (step.compose (identity Γ)).denotes source target ↔ step.denotes source target := by
  rw [compose_denotes_iff]
  constructor
  · rintro ⟨middle, hs, hid⟩
    rw [identity_denotes_iff] at hid
    subst target
    exact hs
  · intro hs
    exact ⟨target, hs, (identity_denotes_iff target target).2 rfl⟩

theorem compose_assoc_denotes_iff {Γ : Ctx} (a b c : QFAbvStep Γ)
    (source target : Env Γ) :
    ((a.compose b).compose c).denotes source target ↔
      (a.compose (b.compose c)).denotes source target := by
  simp only [compose_denotes_iff]
  constructor
  · rintro ⟨middle₂, ⟨middle₁, ha, hb⟩, hc⟩
    exact ⟨middle₁, ha, middle₂, hb, hc⟩
  · rintro ⟨middle₁, ha, middle₂, hb, hc⟩
    exact ⟨middle₂, ⟨middle₁, ha, hb⟩, hc⟩

theorem compositionDenotationLaw_holds : compositionDenotationLaw := by
  intro Γ left right source target
  exact compose_denotes_iff left right source target

theorem identityDenotationLaw_holds : identityDenotationLaw := by
  intro Γ source target
  exact identity_denotes_iff source target

theorem associativityDenotationLaw_holds : associativityDenotationLaw := by
  intro Γ a b c source target
  exact compose_assoc_denotes_iff a b c source target

end QFAbvStep

abbrev QFAbvSegment (Γin Γbody Γout : Ctx) :=
  Ayxg.Segment (Env Γin) (Env Γbody) (Env Γout)
    (QFAbvStep Γbody) (QFAbvAdapter Γin Γbody) (QFAbvAdapter Γbody Γout)

namespace QFAbvSegment

def denotes {Γin Γbody Γout : Ctx} (segment : QFAbvSegment Γin Γbody Γout)
    (source : Env Γin) (target : Env Γout) : Prop :=
  Ayxg.Segment.denotes segment
    (fun source step target => step.denotes source target)
    (fun source step target => step.denotes source target)
    (fun source adapter target => adapter.denotes source target) source target

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
