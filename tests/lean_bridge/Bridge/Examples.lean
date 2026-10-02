import Ayxg.STS
import Ayxg.QfAbv.Subst
import Ayxg.LTS.QfAbv.SymbolicTransitionSystem

namespace Bridge.Examples
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

def difference : Expr ctx (.bv 8) := .bvBin .sub 8 (.var .here) (.var (.there .here))
example : Eval.eval env (Expr.subst swap difference) = BitVec.ofNat 8 (4 - 3) := by
  exact Expr.eval_subst swap env difference

-- The higher-order renaming/substitution theorems also recurse under letPar;
-- instantiate them on the shadowing example to keep this path checked.
example : Eval.eval env (Expr.rename (fun v => v) parallelShadow) =
    Eval.eval env parallelShadow := by
  apply Expr.eval_rename (fun v => v) env env
  · intro s v
    rfl

/- Small trace examples for the generic LTS constructors: branching, cycles,
   label order, concatenation, and a dead end. -/
def graph : LTS Nat Bool where
  Tr source label target :=
    (source = 0 ∧ label = false ∧ target = 1) ∨
    (source = 0 ∧ label = true ∧ target = 2) ∨
    (source = 1 ∧ label = false ∧ target = 1) ∨
    (source = 2 ∧ label = false ∧ target = 1)

example : graph.ReachableFrom 1 1 := .refl
example : graph.ReachableFrom 0 1 :=
  LTS.ReachableFrom.step (s := 0) (s' := 1) (l := false) .refl (by simp [graph])
example : graph.ReachableFrom 0 2 :=
  LTS.ReachableFrom.step (s := 0) (s' := 2) (l := true) .refl (by simp [graph])
example : graph.IsTrace 0 [] 0 := .nil 0
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

/- Directly instantiate the symbolic-label composition and legacy control/run bridges. -/
def identityLabel : SymbolicLabel ctx := SymbolicLabel.identity ctx
example : (identityLabel.compose identityLabel).denotes env env := by
  apply (SymbolicLabel.compose_denotes_iff identityLabel identityLabel env env).2
  exact ⟨env, (SymbolicLabel.identity_denotes_iff env env).2 rfl,
    (SymbolicLabel.identity_denotes_iff env env).2 rfl⟩

def sourceConfig : LTS.QfAbv.Config Nat ctx := ⟨0, env⟩
def targetConfig : LTS.QfAbv.Config Nat ctx := ⟨1, env⟩
def legacyEdge : LTS.QfAbv.SymbolicTransition Nat ctx := ⟨0, some 1, identityLabel⟩
def legacySystem : LTS.QfAbv.SymbolicTransitionSystem Nat ctx
    (LTS.QfAbv.SymbolicTransition Nat ctx) :=
  LTS.QfAbv.SymbolicTransitionSystem.legacy
    (fun control => if control == 0 then [legacyEdge] else [])
example : legacyEdge.nextConfig sourceConfig = targetConfig := rfl
example (run : LTS.QfAbv.SymbolicTransitionSystem.Run legacySystem sourceConfig
    labels targetConfig) : legacySystem.toLTS.IsTrace sourceConfig labels targetConfig :=
  LTS.QfAbv.SymbolicTransitionSystem.Run.toTrace run
