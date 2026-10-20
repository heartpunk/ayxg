import Ayxg.LTS.QfAbv.RegionPre
import Ayxg.LTS.QfAbv.RegionEmpty
import Ayxg.LTS.QfAbv.RegionObservables

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

/-- Semantic Henzinger–Majumdar–Raskin region-algebra laws for an existing
canonical QF_ABV guarded-update graph. Complete finite enumerations certify
the Boolean emptiness scan; an explicit observable family supplies the paper's
observations. The states and transition relation remain those of `system.toLTS`.

This structure does not establish effective encodings or executable
implementations of arbitrary caller-supplied `Region.formulaAt`, `system.transAt`,
or `FPInterpretation` functions. Those are needed for the paper's computability
requirements. -/
structure RegionAlgebra (C : Type) (Γ : Ctx)
    [DecidableEq C] [_root_.Ayxg.QfAbv.FPInterpretation] where
  system : SymbolicTransitionSystem C Γ (SymbolicTransition C Γ)
  canonical : system.edgeSemantics = SymbolicTransition.edgeSemantics
  controls : List C
  controls_complete : ∀ c : C, c ∈ controls
  envs : List (Env Γ)
  envs_complete : ∀ env : Env Γ, env ∈ envs
  observables : Region.Observables C Γ

namespace RegionAlgebra

/-- Existential one-step predecessor, computed from the existing edge lists. -/
def pre {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (target : Region C Γ) : Region C Γ :=
  Region.pre algebra.system algebra.canonical target

/-- Decide region emptiness using the supplied complete finite state factors. -/
def empty {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (region : Region C Γ) : Bool :=
  region.empty algebra.controls algebra.envs

/-- Decide whether a concrete configuration belongs to a region. -/
def member {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (_algebra : RegionAlgebra C Γ) (region : Region C Γ)
    (cfg : Config C Γ) : Bool :=
  region.member cfg

/-- `pre` denotes exactly the concrete predecessors in the original LTS. -/
theorem holds_pre_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (target : Region C Γ)
    (source : Config C Γ) :
    (algebra.pre target).Holds source ↔
      ∃ edge successor,
        algebra.system.toLTS.Tr source edge successor ∧ target.Holds successor :=
  Region.holds_pre_iff algebra.system algebra.canonical target source

/-- `empty` returns true exactly for regions with no concrete members. -/
theorem empty_eq_true_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (region : Region C Γ) :
    algebra.empty region = true ↔
      ∀ cfg : Config C Γ, ¬ region.Holds cfg :=
  Region.empty_eq_true_iff algebra.controls algebra.envs
    algebra.controls_complete algebra.envs_complete region

/-- `member` returns true exactly for configurations in a region. -/
theorem member_eq_true_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (region : Region C Γ)
    (cfg : Config C Γ) :
    algebra.member region cfg = true ↔ region.Holds cfg :=
  Region.member_eq_true_iff region cfg

/-- Region intersection is semantic set intersection. -/
theorem holds_inter_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (_algebra : RegionAlgebra C Γ) (left right : Region C Γ)
    (cfg : Config C Γ) :
    (left.inter right).Holds cfg ↔ left.Holds cfg ∧ right.Holds cfg :=
  Region.holds_inter_iff left right cfg

/-- Region difference is semantic set difference. -/
theorem holds_diff_iff {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (_algebra : RegionAlgebra C Γ) (left right : Region C Γ)
    (cfg : Config C Γ) :
    (left.diff right).Holds cfg ↔ left.Holds cfg ∧ ¬ right.Holds cfg :=
  Region.holds_diff_iff left right cfg

/-- The observables cover the existing configurations. -/
theorem observable_cover {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (cfg : Config C Γ) :
    ∃ region ∈ algebra.observables.regions, region.Holds cfg :=
  algebra.observables.covers cfg

/-- Each observable has a denotational complement among the observables. -/
theorem observable_complement {C : Type} [DecidableEq C]
    [_root_.Ayxg.QfAbv.FPInterpretation] {Γ : Ctx}
    (algebra : RegionAlgebra C Γ) (region : Region C Γ)
    (hregion : region ∈ algebra.observables.regions) :
    ∃ complement ∈ algebra.observables.regions,
      ∀ cfg : Config C Γ,
        complement.Holds cfg ↔ ¬ region.Holds cfg :=
  algebra.observables.complementClosed region hregion

end RegionAlgebra

end QfAbv
end LTS
end Ayxg
