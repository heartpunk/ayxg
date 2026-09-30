import Ayxg.STS
import Ayxg.QfAbv.SymbolicLabel

namespace Ayxg.QfAbv

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

end QFAbvStep

/-- Full-state STS: PC/control, when present, is a declaration inside Γ. -/
structure QFAbvSTS (Γ : Ctx) where
  steps : List (QFAbvStep Γ Γ)

namespace QFAbvSTS

def toSTS {Γ : Ctx} (model : QFAbvSTS Γ) : Ayxg.STS (Env Γ) (QFAbvStep Γ Γ) where
  steps := model.steps

def toLTS {Γ : Ctx} (model : QFAbvSTS Γ) : Ayxg.LTS (Env Γ) (QFAbvStep Γ Γ) :=
  model.toSTS.toLTS (fun source step target => step.denotes source target)

end QFAbvSTS

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
