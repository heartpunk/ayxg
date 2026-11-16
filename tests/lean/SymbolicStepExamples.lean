import Ayxg.LTS.QfAbv.SymbolicStep
import Ayxg.LTS.QfAbv.STSBridge

namespace Ayxg.LTS.QfAbv.SymbolicStepExamples

open _root_.Ayxg.QfAbv

def reg : Ctx := [⟨"x", .bv 8⟩]
def empty : Ctx := []
def input : QFAbvAdapter reg reg :=
  ⟨.boolLit true, .cons (.bvBin .add 8 (.var .here) (.bvLit 8 1)) .nil⟩
def twice : QFAbvStep reg :=
  ⟨.eqBv 8 (.var .here) (.bvLit 8 4),
   .cons (.bvBin .mul 8 (.var .here) (.bvLit 8 2)) .nil⟩
def other : QFAbvStep reg :=
  ⟨.boolNot (.eqBv 8 (.var .here) (.bvLit 8 4)),
   .cons (.bvLit 8 99) .nil⟩

-- Adapters support genuinely heterogeneous source and output contexts.
example : QFAbvAdapter empty reg :=
  ⟨.boolLit true, .cons (.bvLit 8 0) .nil⟩

/-- error: Application type mismatch: The argument
  StateUpdate.identity empty
has type
  StateUpdate empty empty
but is expected to have type
  StateUpdate reg reg
in the application
  { guard := Expr.boolLit true, update := StateUpdate.identity empty }
-/
#guard_msgs in
example : QFAbvStep reg := ⟨.boolLit true, StateUpdate.identity empty⟩

variable [FPInterpretation]

def edgeTwice : SymbolicTransition Unit reg := QFAbvStep.toControlEdge twice
def edgeOther : SymbolicTransition Unit reg := QFAbvStep.toControlEdge other
def model : SymbolicTransitionSystem Unit reg (SymbolicTransition Unit reg) :=
  Ayxg.QfAbv.toControlSystem [twice, other]
def emptyModel : SymbolicTransitionSystem Unit reg (SymbolicTransition Unit reg) :=
  Ayxg.QfAbv.toControlSystem []
def first : QFAbvAdapter reg reg :=
  (model.symbolicStep input).headD
    ⟨edgeTwice, QFAbvAdapter.identity reg⟩ |>.step
def second : QFAbvAdapter reg reg :=
  (model.symbolicStep input).getD 1
    ⟨edgeOther, QFAbvAdapter.identity reg⟩ |>.step

-- The returned family retains source edge order, labels, and both branches.
example : model.symbolicStep input =
    [⟨edgeTwice, input.composeStep twice⟩, ⟨edgeOther, input.composeStep other⟩] := rfl
example : (model.symbolicStep input).length = 2 := by
  rw [SymbolicTransitionSystem.symbolicStep_length]
  rfl
example : emptyModel.symbolicStep input = [] := rfl

-- Composition is (x + 1) * 2 = 8, not x * 2 + 1 = 7.
example : Env.lookup (first.update.eval (.cons (3 : BitVec 8) .nil)) .here = (8 : BitVec 8) := rfl
-- Guard tests updated x = 4, rather than original x = 4.
example : Eval.evalBool (.cons (3 : BitVec 8) .nil) first.guard = true := rfl
example : Eval.evalBool (.cons (4 : BitVec 8) .nil) first.guard = false := rfl
example : Eval.evalBool (.cons (3 : BitVec 8) .nil) second.guard = false := rfl
example : Eval.evalBool (.cons (4 : BitVec 8) .nil) second.guard = true := rfl
example : Env.lookup (second.update.eval (.cons (4 : BitVec 8) .nil)) .here = (99 : BitVec 8) := rfl

-- Input rejection remains rejection even when the source edge is enabled.
def rejected : QFAbvAdapter reg reg := ⟨.boolLit false, input.update⟩
example : Eval.evalBool (.cons (3 : BitVec 8) .nil)
    ((model.symbolicStep rejected).headD ⟨edgeTwice, input⟩).step.guard = false := rfl

-- An empty source system has no concrete labeled transition.
example (ρ : Env reg) (t : Env reg) :
    ¬ (∃ successor ∈ emptyModel.symbolicStep input,
      successor.step.denotes ρ t) := by
  simp [emptyModel, SymbolicTransitionSystem.symbolicStep,
    Ayxg.QfAbv.toControlSystem, SymbolicTransitionSystem.legacy,
    ShareCommon.shareCommon']

-- Memory arrays remain supported, and completeness retains the exact edge.
example {Γinput Γ : Ctx}
    (m : SymbolicTransitionSystem Unit Γ (SymbolicTransition Unit Γ))
    (i : QFAbvAdapter Γinput Γ) (ρ : Env Γinput) (edge : SymbolicTransition Unit Γ)
    (t : Env Γ) (h : Eval.evalBool ρ i.guard = true)
    (step : m.toLTS.Tr ⟨(), i.update.eval ρ⟩ edge ⟨(), t⟩) :
    ∃ successor ∈ m.symbolicStep i,
      successor.edge = edge ∧ successor.step.denotes ρ t :=
  (SymbolicTransitionSystem.symbolicStep_denotes_iff m i ρ edge t).2 ⟨h, step⟩

-- Runtime-only allocation check, not a proof mechanism: duplicate equal
-- successors still share an object. Semantic proofs do not depend on pointers.
unsafe def checkSharing : IO Unit := do
  let outputs := (Ayxg.QfAbv.toControlSystem [twice, twice]).symbolicStep input
  match outputs with
  | a :: b :: [] =>
      if ptrAddrUnsafe a.step == ptrAddrUnsafe b.step then
        IO.println "shared successor object: PASS"
      else throw (IO.userError "equal successors were not shared")
  | _ => throw (IO.userError "wrong successor count")

#eval checkSharing

end Ayxg.LTS.QfAbv.SymbolicStepExamples
