import Ayxg.QfAbv.SymbolicLabel

namespace Ayxg
namespace LTS
namespace QfAbv

variable [_root_.Ayxg.QfAbv.FPInterpretation]

open _root_.Ayxg.QfAbv

/-- Flat QF_ABV configuration for the current symbolic transition system.

`control` is a control value. `env` is the QF_ABV environment value. Neither
field is a K-style cell, and this structure is intentionally not a K cell
configuration. If/when this project needs literal cells, model them explicitly. -/
structure Config (C : Type) (Γ : Ctx) where
  control : C
  env : Env Γ

/-- Value-owned semantics for a complete symbolic edge type.

The record deliberately exposes only the edge source, its QF_ABV
guard/update payload, and its next-control computation. Guard evaluation,
simultaneous environment update, complete successor construction, and
relational denotation remain centralized below. -/
structure SymbolicEdgeSemantics (C : Type) (Γ : Ctx) (E : Type) where
  source : E → C
  symbolicLabel : E → SymbolicLabel Γ
  nextControl : E → Config C Γ → C

namespace SymbolicEdgeSemantics

/-- Apply an edge's target/control computation and simultaneous update to the
same pre-state configuration. -/
def nextConfig {C : Type} {Γ : Ctx} {E : Type}
    (sem : SymbolicEdgeSemantics C Γ E) (edge : E)
    (sourceCfg : Config C Γ) : Config C Γ :=
  { control := sem.nextControl edge sourceCfg
    env := (sem.symbolicLabel edge).update.eval sourceCfg.env }

/-- Central relational meaning of a symbolic edge. -/
def denotes {C : Type} {Γ : Ctx} {E : Type}
    (sem : SymbolicEdgeSemantics C Γ E) (edge : E)
    (sourceCfg successorCfg : Config C Γ) : Prop :=
  sem.source edge = sourceCfg.control
    ∧ Eval.evalBool sourceCfg.env (sem.symbolicLabel edge).guard = true
    ∧ sem.nextConfig edge sourceCfg = successorCfg

/-- A denoting edge's projected symbolic label denotes the environment
projection of the complete endpoint configurations. -/
theorem denotes_symbolicLabel {C : Type} {Γ : Ctx} {E : Type}
    {sem : SymbolicEdgeSemantics C Γ E} {edge : E}
    {sourceCfg successorCfg : Config C Γ}
    (h : sem.denotes edge sourceCfg successorCfg) :
    (sem.symbolicLabel edge).denotes sourceCfg.env successorCfg.env := by
  rcases h with ⟨_, hguard, hnext⟩
  constructor
  · exact hguard
  · rw [← hnext]
    rfl

end SymbolicEdgeSemantics

/-- Symbolic transition edge over a typed QF_ABV environment.

The source and target are graph/control-flow structure; `label` is the symbolic
guard/update transformer payload. -/
structure SymbolicTransition (C : Type) (Γ : Ctx) where
  src : C
  tgt : Option C
  label : SymbolicLabel Γ

namespace SymbolicTransition

/-- Canonical semantics for the legacy concrete/retain-control edge.

The public `tgt := none` convention deliberately retains the incoming control
value. -/
def edgeSemantics {C : Type} {Γ : Ctx} :
    SymbolicEdgeSemantics C Γ (SymbolicTransition C Γ) where
  source := SymbolicTransition.src
  symbolicLabel := SymbolicTransition.label
  nextControl := fun edge sourceCfg => edge.tgt.getD sourceCfg.control

@[simp] theorem edgeSemantics_source {C : Type} {Γ : Ctx}
    (edge : SymbolicTransition C Γ) :
    edgeSemantics.source edge = edge.src := rfl

@[simp] theorem edgeSemantics_symbolicLabel {C : Type} {Γ : Ctx}
    (edge : SymbolicTransition C Γ) :
    edgeSemantics.symbolicLabel edge = edge.label := rfl

@[simp] theorem edgeSemantics_nextControl {C : Type} {Γ : Ctx}
    (edge : SymbolicTransition C Γ) (sourceCfg : Config C Γ) :
    edgeSemantics.nextControl edge sourceCfg =
      edge.tgt.getD sourceCfg.control := rfl

/-- Compose the symbolic labels carried by a nonempty transition path.

This deliberately summarizes only the QF_ABV guard/update payloads. It does
not construct a summary transition edge or summarize control movement. -/
def composeLabels {C : Type} {Γ : Ctx} (head : SymbolicTransition C Γ)
    (tail : List (SymbolicTransition C Γ)) : SymbolicLabel Γ :=
  SymbolicLabel.composeNonempty head.label (tail.map SymbolicTransition.label)

/-- Apply a symbolic transition's update and target convention. -/
def nextConfig {C : Type} {Γ : Ctx} (t : SymbolicTransition C Γ)
    (s : Config C Γ) : Config C Γ :=
  { control := t.tgt.getD s.control
    env := t.label.update.eval s.env }

theorem nextConfig_eq {C : Type} {Γ : Ctx}
    (t : SymbolicTransition C Γ) (sourceCfg : Config C Γ) :
    t.nextConfig sourceCfg =
      { control := t.tgt.getD sourceCfg.control
        env := t.label.update.eval sourceCfg.env } := rfl

@[simp] theorem edgeSemantics_nextConfig {C : Type} {Γ : Ctx}
    (t : SymbolicTransition C Γ) (sourceCfg : Config C Γ) :
    edgeSemantics.nextConfig t sourceCfg = t.nextConfig sourceCfg := rfl

/-- Relational meaning of a symbolic transition edge. -/
def denotes {C : Type} {Γ : Ctx} (t : SymbolicTransition C Γ)
    (s s' : Config C Γ) : Prop :=
  edgeSemantics.denotes t s s'

/-- A denoting symbolic transition's label denotes the environment projection
of the endpoint configurations. -/
theorem denotes_label {C : Type} {Γ : Ctx} {t : SymbolicTransition C Γ}
    {s s' : Config C Γ} (h : t.denotes s s') : t.label.denotes s.env s'.env := by
  exact SymbolicEdgeSemantics.denotes_symbolicLabel h

/-- Regression theorem for the latent legacy retain-control convention. -/
theorem nextConfig_control_of_tgt_none {C : Type} {Γ : Ctx}
    (t : SymbolicTransition C Γ) (sourceCfg : Config C Γ)
    (h : t.tgt = none) :
    (t.nextConfig sourceCfg).control = sourceCfg.control := by
  simp [nextConfig, h]

end SymbolicTransition

end QfAbv
end LTS
end Ayxg
