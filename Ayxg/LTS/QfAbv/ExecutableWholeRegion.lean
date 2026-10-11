import Ayxg.LTS.QfAbv.WholeStateRegionStep
import Ayxg.QfAbv.ExecutableFP

namespace Ayxg.LTS.QfAbv

open _root_.Ayxg.QfAbv

-- This module fixes one executable interpretation of the SMT operations whose
-- results are underspecified. It does not change other models' interpretations.
local instance : FPInterpretation := FPInterpretation.executableChoice

/-- A whole-state HMR region is finite Boolean expression syntax. -/
structure WholeRegion (Γ : Ctx) where
  formula : Expr Γ .bool

namespace WholeRegion

def toRegion {Γ : Ctx} (region : WholeRegion Γ) : Region Unit Γ where
  formulaAt := fun _ => region.formula

def Holds {Γ : Ctx} (region : WholeRegion Γ) (env : Env Γ) : Prop :=
  Eval.evalBool env region.formula = true

/-- Executable membership in a syntax-backed region. -/
def member {Γ : Ctx} (region : WholeRegion Γ) (env : Env Γ) : Bool :=
  Eval.evalBool env region.formula

/-- Executable emptiness scan over every value of the finite state context. -/
def empty {Γ : Ctx} (region : WholeRegion Γ) : Bool :=
  (enumerateEnv Γ).all fun env => !region.member env

def inter {Γ : Ctx} (left right : WholeRegion Γ) : WholeRegion Γ :=
  ⟨.boolAnd left.formula right.formula⟩

def diff {Γ : Ctx} (left right : WholeRegion Γ) : WholeRegion Γ :=
  ⟨.boolAnd left.formula (.boolNot right.formula)⟩

/-- Finite predecessor construction over the model's actual guarded-rule list.
`Region.pre` folds that list into a Boolean formula; the sole control site is
selected here, so the returned value is expression syntax rather than a
function-valued region. -/
def pre {Γ : Ctx} (model : QFAbvSTS Γ)
    (target : WholeRegion Γ) : WholeRegion Γ :=
  ⟨(Region.pre model.toControlSystem target.toRegion).formulaAt ()⟩

theorem member_eq_true_iff {Γ : Ctx} (region : WholeRegion Γ)
    (env : Env Γ) : region.member env = true ↔ region.Holds env := by
  rfl

theorem empty_eq_true_iff {Γ : Ctx} (region : WholeRegion Γ) :
    region.empty = true ↔ ∀ env : Env Γ, ¬ region.Holds env := by
  simp only [empty, List.all_eq_true]
  constructor
  · intro h env
    have hb := h env (mem_enumerateEnv env)
    simpa [member, Holds] using hb
  · intro h env _
    simpa [member, Holds] using h env

theorem holds_inter_iff {Γ : Ctx} (left right : WholeRegion Γ)
    (env : Env Γ) :
    (left.inter right).Holds env ↔ left.Holds env ∧ right.Holds env := by
  simp [Holds, inter, Eval.evalBool, Eval.eval]

theorem holds_diff_iff {Γ : Ctx} (left right : WholeRegion Γ)
    (env : Env Γ) :
    (left.diff right).Holds env ↔ left.Holds env ∧ ¬ right.Holds env := by
  simp [Holds, diff, Eval.evalBool, Eval.eval]

/-- Exact one-step HMR predecessor for the original whole-state transition
relation, using the same finite expression syntax as the other operations. -/
theorem holds_pre_iff {Γ : Ctx} (model : QFAbvSTS Γ)
    (target : WholeRegion Γ) (source : Env Γ) :
    (pre model target).Holds source ↔
      ∃ result : Env Γ,
        model.toLTS.canStep source result ∧ target.Holds result := by
  have hpre := Region.holds_pre_iff model.toControlSystem rfl
    target.toRegion ⟨(), source⟩
  constructor
  · intro h
    obtain ⟨edge, successor, hstep, htarget⟩ := hpre.mp h
    cases successor with
    | mk control result =>
      cases control
      refine ⟨result, ?_, ?_⟩
      · exact (model.toControlSystem_canStep_iff source result).mpr ⟨edge, hstep⟩
      · exact htarget
  · rintro ⟨result, hstep, htarget⟩
    obtain ⟨edge, hedge⟩ := (model.toControlSystem_canStep_iff source result).mp hstep
    exact hpre.mpr ⟨edge, ⟨(), result⟩, hedge, htarget⟩

end WholeRegion

/-- Finite observables in the same syntax-backed region representation. -/
structure WholeObservables (Γ : Ctx) where
  regions : List (WholeRegion Γ)
  covers : ∀ env : Env Γ,
    ∃ region ∈ regions, region.Holds env
  complementClosed : ∀ region ∈ regions,
    ∃ complement ∈ regions,
      ∀ env : Env Γ, complement.Holds env ↔ ¬ region.Holds env

/-- The effective HMR tuple for one finite whole-state QF_ABV model. -/
structure ExecutableWholeStateAlgebra (Γ : Ctx) where
  system : QFAbvSTS Γ
  observables : WholeObservables Γ

end Ayxg.LTS.QfAbv
