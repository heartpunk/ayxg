import Ayxg.STS
import Ayxg.QfAbv.STS
import Ayxg.QfAbv.Subst
import Ayxg.LTS.QfAbv.SymbolicTransitionSystem

namespace Bridge.Examples

variable [Ayxg.QfAbv.FPInterpretation]
open Ayxg Ayxg.QfAbv

def ctx : Ctx := [{ name := "x", sort := .bv 8 }, { name := "y", sort := .bv 8 }]
def env : Env ctx := .cons (BitVec.ofNat 8 3) (.cons (BitVec.ofNat 8 4) .nil)
def bindings : Bindings ctx
    ([{ name := "x", sort := .bv 8 }, { name := "y", sort := .bv 8 }] ++ ctx) :=
  .cons "x" (.bv 8) (.bvLit 8 9)
    (.cons "y" (.bv 8) (.var .here) .nil)

def parallelShadow : Expr ctx .bool :=
  .letPar bindings
    (.boolAnd
      (.eqBv 8 (.var .here) (.bvLit 8 9))
      (.eqBv 8 (.var (.there .here)) (.bvLit 8 3)))

example : Eval.eval env parallelShadow = true := rfl

-- Renaming a free variable and evaluating in the renamed context preserves its value.
def src : Ctx := [{ name := "x", sort := .bv 8 }]
def dst : Ctx := [{ name := "y", sort := .bv 8 }]
def renameXY : Renaming src dst := by
  intro s v
  cases v with
  | here => exact .here
  | there impossible => nomatch impossible
def srcEnv : Env src := .cons (BitVec.ofNat 8 7) .nil
def dstEnv : Env dst := .cons (BitVec.ofNat 8 7) .nil
def renameAgreement : ∀ {s} (v : Var src s),
    Env.lookup dstEnv (renameXY v) = Env.lookup srcEnv v := by
  intro s v
  cases v with
  | here => rfl
  | there impossible => nomatch impossible

def freeX : Expr src (.bv 8) := .var .here
example : Eval.eval dstEnv (Expr.rename renameXY freeX) = Eval.eval srcEnv freeX :=
  Expr.eval_rename renameXY srcEnv dstEnv renameAgreement freeX

-- Substitution swaps both variables simultaneously; it does not recursively
-- substitute the replacement for y after replacing x.
def swap : Subst ctx ctx
  | _, .here => .var (.there .here)
  | _, .there .here => .var .here
  | _, .there (.there v) => nomatch v

def freeXUnderLetPar : Expr ctx (.bv 8) :=
  .letPar (.cons "z" (.bv 8) (.bvLit 8 1) .nil)
    (.bvBin .add 8 (.var .here) (.var (.there .here)))

def difference : Expr ctx (.bv 8) := .bvBin .sub 8 (.var .here) (.var (.there .here))
example : Eval.eval env (Expr.subst swap difference) = BitVec.ofNat 8 (4 - 3) := by
  exact Expr.eval_subst swap env difference
example : Eval.eval env (Expr.subst swap parallelShadow) = false := by
  rw [Expr.eval_subst swap env parallelShadow]
  rfl
example : Eval.eval env (Expr.subst swap freeXUnderLetPar) = BitVec.ofNat 8 5 := by
  rw [Expr.eval_subst swap env freeXUnderLetPar]
  rfl

-- The higher-order renaming/substitution theorems also recurse under letPar;
-- instantiate them on the shadowing example to keep this path checked.
example : Eval.eval env (Expr.rename (fun v => v) parallelShadow) =
    Eval.eval env parallelShadow := by
  apply Expr.eval_rename (fun v => v) env env
  · intro s v
    rfl

def swapRenaming : Renaming ctx ctx
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there v) => nomatch v
def swappedEnv : Env ctx := .cons (BitVec.ofNat 8 4) (.cons (BitVec.ofNat 8 3) .nil)
def swapAgreement : ∀ {s} (v : Var ctx s),
    Env.lookup swappedEnv (swapRenaming v) = Env.lookup env v := by
  intro s v
  cases v with
  | here => rfl
  | there v =>
    cases v with
    | here => rfl
    | there impossible => nomatch impossible
example : Eval.eval swappedEnv (Expr.rename swapRenaming freeXUnderLetPar) =
    Eval.eval env freeXUnderLetPar :=
  Expr.eval_rename swapRenaming env swappedEnv swapAgreement freeXUnderLetPar

/- Small trace examples for the generic LTS constructors: branching, cycles,
   label order, concatenation, and a dead end. -/
def graph : LTS Nat Bool where
  Tr source label target :=
    (source = 0 ∧ label = false ∧ target = 1) ∨
    (source = 0 ∧ label = true ∧ target = 2) ∨
    (source = 1 ∧ label = false ∧ target = 1) ∨
    (source = 2 ∧ label = false ∧ target = 1)
def genericView : ControlView Nat Nat Nat := ⟨1⟩
example : genericView.observe (fun view state => view + state) 2 = 3 := rfl

example : graph.ReachableFrom 1 1 := .refl
example : graph.ReachableFrom 0 1 :=
  LTS.ReachableFrom.step (s := 0) (s' := 1) (l := false) .refl (by simp [graph])
example : graph.ReachableFrom 0 2 :=
  LTS.ReachableFrom.step (s := 0) (s' := 2) (l := true) .refl (by simp [graph])
example : graph.IsTrace 0 [] 0 := .nil 0
example : graph.IsTrace 0 [true] 2 :=
  LTS.IsTrace.cons true [] (s₁ := 0) (s₂ := 2) (s₃ := 2)
    (by simp [graph]) (.nil 2)
example : graph.IsTrace 0 [false, false] 1 := by
  exact LTS.IsTrace.cons false [false] (s₁ := 0) (s₂ := 1) (s₃ := 1)
    (by simp [graph])
    (LTS.IsTrace.cons false [] (s₁ := 1) (s₂ := 1) (s₃ := 1)
      (by simp [graph]) (.nil 1))
example : graph.IsTrace 0 [true, false] 1 := by
  exact LTS.IsTrace.cons true [false] (s₁ := 0) (s₂ := 2) (s₃ := 1)
    (by simp [graph])
    (LTS.IsTrace.cons false [] (s₁ := 2) (s₂ := 1) (s₃ := 1)
      (by simp [graph]) (.nil 1))
example : graph.IsTrace 0 [false, false] 1 :=
  LTS.IsTrace.append
    (LTS.IsTrace.cons false [] (s₁ := 0) (s₂ := 1) (s₃ := 1)
      (by simp [graph]) (.nil 1))
    (LTS.IsTrace.cons false [] (s₁ := 1) (s₂ := 1) (s₃ := 1)
      (by simp [graph]) (.nil 1))
example : ¬ ∃ label target, graph.Tr 3 label target := by
  rintro ⟨label, target, h⟩
  simp [graph] at h

-- STS.Runs includes the zero-step path and only admits listed labels.
def graphSTS : STS Nat Bool := ⟨[false, true]⟩
def graphSemantics : Nat → Bool → Nat → Prop := graph.Tr
example : graphSTS.Runs graphSemantics 0 0 := .refl
example : graphSTS.Runs graphSemantics 0 2 := by
  simpa [STS.Runs, STS.toLTS, graphSTS, graphSemantics] using
    (LTS.ReachableFrom.step (lts := graphSTS.toLTS graphSemantics)
      (s := 0) (s' := 2) (l := true) .refl
      ⟨by decide, by simp [graph, graphSemantics]⟩)

/- Direct examples use Segment.denotes itself, including empty and one-step body runs. -/
def exampleSegment : Segment Nat Nat Nat Nat Nat Nat :=
  ⟨⟨0⟩, ⟨[1]⟩, [⟨0⟩]⟩
def entryRel (input label body : Nat) : Prop := body = input + label
def bodyRel (source label target : Nat) : Prop := target = source + label
def exitRel (body label output : Nat) : Prop := output = body + label

example : exampleSegment.denotes entryRel bodyRel exitRel 4 4 := by
  unfold Segment.denotes Adapter.denotes
  refine ⟨4, 4, ?_, .refl, ⟨⟨0⟩, by simp [exampleSegment], ?_⟩⟩
  · simp [exampleSegment, entryRel]
  · simp [exitRel]
example : exampleSegment.denotes entryRel bodyRel exitRel 4 5 := by
  unfold Segment.denotes Adapter.denotes
  refine ⟨4, 5, ?_, ?_, ⟨⟨0⟩, by simp [exampleSegment], ?_⟩⟩
  · simp [exampleSegment, entryRel]
  · exact LTS.ReachableFrom.step (lts := exampleSegment.body.toLTS bodyRel)
      (start := 4) (s := 4) (s' := 5) (l := 1) .refl
      ⟨by simp [exampleSegment], by simp [bodyRel]⟩
  · simp [exitRel]
example : ¬ (exampleSegment.denotes (fun _ _ _ => False) bodyRel exitRel 4 4) := by
  intro h
  rcases h with ⟨first, _, hentry, _, _⟩
  exact hentry
example : ¬ (exampleSegment.denotes entryRel bodyRel (fun _ _ _ => False) 4 4) := by
  intro h
  rcases h with ⟨_, _, _, _, ⟨exit, _, hExit⟩⟩
  exact hExit

/- The generic hierarchy accepts empty, chain, diamond, shared-child and
   multiple-root layouts while its proposition rejects bad order and keys. -/
def dagEmpty : SegmentDAG Nat String where
  nodes := []
  roots := []
  ordered := by simp [SegmentNode.Ordered]
  rootsPresent := by intro root h; simp at h

def dagLeaf : SegmentDAG Nat String where
  nodes := [⟨0, "leaf", []⟩]
  roots := [0]
  ordered := by simp [SegmentNode.Ordered]
  rootsPresent := by
    intro root h
    simp at h
    subst root
    exact ⟨⟨0, "leaf", []⟩, by simp, rfl⟩

def dagChain : SegmentDAG Nat String where
  nodes := [⟨0, "leaf", []⟩, ⟨1, "middle", [0]⟩, ⟨2, "root", [1]⟩]
  roots := [2]
  ordered := by simp [SegmentNode.Ordered]
  rootsPresent := by
    intro root h
    simp at h
    subst root
    exact ⟨⟨2, "root", [1]⟩, by simp, rfl⟩

def dagDiamond : SegmentDAG Nat String where
  nodes := [⟨0, "left", []⟩, ⟨1, "right", []⟩, ⟨2, "join", [0, 1]⟩]
  roots := [2]
  ordered := by simp [SegmentNode.Ordered]
  rootsPresent := by
    intro root h
    simp at h
    subst root
    exact ⟨⟨2, "join", [0, 1]⟩, by simp, rfl⟩

def dagShared : SegmentDAG Nat String where
  nodes := [⟨0, "shared", []⟩, ⟨1, "parent-a", [0]⟩,
            ⟨2, "parent-b", [0]⟩]
  roots := [1, 2]
  ordered := by simp [SegmentNode.Ordered]
  rootsPresent := by
    intro root h
    simp at h
    rcases h with rfl | rfl
    · exact ⟨⟨1, "parent-a", [0]⟩, by simp, rfl⟩
    · exact ⟨⟨2, "parent-b", [0]⟩, by simp, rfl⟩

example : dagEmpty.nodes = [] := rfl
example : dagLeaf.nodes = [⟨0, "leaf", []⟩] := rfl
example : dagChain.nodes = [⟨0, "leaf", []⟩, ⟨1, "middle", [0]⟩,
                             ⟨2, "root", [1]⟩] := rfl
example : dagDiamond.nodes = [⟨0, "left", []⟩, ⟨1, "right", []⟩,
                               ⟨2, "join", [0, 1]⟩] := rfl
example : dagShared.roots = [1, 2] ∧ dagShared.nodes.map SegmentNode.segment =
    ["shared", "parent-a", "parent-b"] := by simp [dagShared]
example : ¬ SegmentNode.Ordered []
    [⟨0, "forward", [1]⟩, ⟨1, "child", []⟩] := by simp [SegmentNode.Ordered]
example : ¬ SegmentNode.Ordered [] [⟨0, "first", []⟩, ⟨0, "duplicate", []⟩] := by
  simp [SegmentNode.Ordered]
example : ¬ SegmentNode.Ordered [] [⟨0, "missing", [9]⟩] := by simp [SegmentNode.Ordered]
example : ¬ (∀ root ∈ [9], ∃ node ∈ dagChain.nodes, node.key = root) := by
  simp [dagChain]

/- Directly instantiate the symbolic-label composition and legacy control/run bridges. -/
def identityLabel : SymbolicLabel ctx := SymbolicLabel.identity ctx
example : (identityLabel.compose identityLabel).denotes env env := by
  apply (SymbolicLabel.compose_denotes_iff identityLabel identityLabel env env).2
  exact ⟨env, (SymbolicLabel.identity_denotes_iff env env).2 rfl,
    (SymbolicLabel.identity_denotes_iff env env).2 rfl⟩

def controlView : QFAbvControlView ctx (.bv 8) := ⟨.var .here⟩
example : controlView.observe env = 3 := rfl

def qfModel : QFAbvSTS ctx := ⟨[QFAbvStep.identity ctx]⟩
example : qfModel.toSTS.steps = [QFAbvStep.identity ctx] := rfl
example : qfModel.toLTS.Tr env (QFAbvStep.identity ctx) env := by
  exact ⟨by simp [qfModel, QFAbvSTS.toSTS],
    (QFAbvStep.identity_denotes_iff env env).2 rfl⟩

def sourceConfig : LTS.QfAbv.Config Nat ctx := ⟨0, env⟩
def targetConfig : LTS.QfAbv.Config Nat ctx := ⟨1, env⟩
def legacyEdge : LTS.QfAbv.SymbolicTransition Nat ctx := ⟨0, some 1, identityLabel⟩
def legacyRetain : LTS.QfAbv.SymbolicTransition Nat ctx := ⟨0, none, identityLabel⟩
def legacySystem : LTS.QfAbv.SymbolicTransitionSystem Nat ctx
    (LTS.QfAbv.SymbolicTransition Nat ctx) :=
  LTS.QfAbv.SymbolicTransitionSystem.legacy
    (fun control => if control == 0 then [legacyEdge] else [])
example : legacyEdge.nextConfig sourceConfig = targetConfig := rfl
example : (legacyRetain.nextConfig sourceConfig).control = sourceConfig.control := by
  exact LTS.QfAbv.SymbolicTransition.nextConfig_control_of_tgt_none
    legacyRetain sourceConfig rfl

def legacyWitness : LTS.QfAbv.SymbolicTransitionSystem.StepWitness
    legacySystem sourceConfig targetConfig := by
  refine ⟨legacyEdge, ?_, ?_⟩
  · simp [legacySystem, legacyEdge, sourceConfig,
      LTS.QfAbv.SymbolicTransitionSystem.legacy]
  · change LTS.QfAbv.SymbolicTransition.edgeSemantics.denotes
      legacyEdge sourceConfig targetConfig
    simp [legacyEdge, sourceConfig, targetConfig, identityLabel,
      LTS.QfAbv.SymbolicTransition.edgeSemantics,
      LTS.QfAbv.SymbolicEdgeSemantics.denotes,
      LTS.QfAbv.SymbolicEdgeSemantics.nextConfig,
      SymbolicLabel.identity, StateUpdate.eval_identity, Eval.eval]

def legacyRun : LTS.QfAbv.SymbolicTransitionSystem.Run
    legacySystem sourceConfig [legacyEdge] targetConfig :=
  .cons legacyWitness .nil
example : legacySystem.toLTS.IsTrace sourceConfig [legacyEdge] targetConfig :=
  LTS.QfAbv.SymbolicTransitionSystem.Run.toTrace legacyRun
example : Nonempty (LTS.QfAbv.SymbolicTransitionSystem.Run
    legacySystem sourceConfig [legacyEdge] targetConfig) :=
  LTS.QfAbv.SymbolicTransitionSystem.Run.exists_of_trace
    (LTS.QfAbv.SymbolicTransitionSystem.Run.toTrace legacyRun)
