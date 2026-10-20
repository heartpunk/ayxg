import Ayxg.LTS.QfAbv.SymbolicStep
import Ayxg.LTS.QfAbv.STSBridge

namespace Ayxg.LTS.QfAbv.SymbolicStepExamples

open _root_.Ayxg.QfAbv

def reg : Ctx := [⟨"x", .bv 8⟩]
def input : QFAbvStep reg reg :=
  ⟨.boolLit true, .cons (.bvBin .add 8 (.var .here) (.bvLit 8 1)) .nil⟩
def twice : QFAbvStep reg reg :=
  ⟨.eqBv 8 (.var .here) (.bvLit 8 4),
   .cons (.bvBin .mul 8 (.var .here) (.bvLit 8 2)) .nil⟩
def other : QFAbvStep reg reg :=
  ⟨.boolNot (.eqBv 8 (.var .here) (.bvLit 8 4)),
   .cons (.bvLit 8 99) .nil⟩

variable [FPInterpretation]

def edgeTwice : SymbolicTransition Unit reg := QFAbvStep.toControlEdge twice
def edgeOther : SymbolicTransition Unit reg := QFAbvStep.toControlEdge other
def model : SymbolicTransitionSystem Unit reg (SymbolicTransition Unit reg) :=
  Ayxg.QfAbv.toControlSystem [twice, other]
def emptyModel : SymbolicTransitionSystem Unit reg (SymbolicTransition Unit reg) :=
  Ayxg.QfAbv.toControlSystem []
def first : QFAbvStep reg reg :=
  (model.symbolicStep input).headD
    ⟨edgeTwice, QFAbvStep.identity reg⟩ |>.step
def second : QFAbvStep reg reg :=
  (model.symbolicStep input).getD 1
    ⟨edgeOther, QFAbvStep.identity reg⟩ |>.step

-- The returned family retains source edge order, labels, and both branches.
example : model.symbolicStep input =
    [⟨edgeTwice, input.compose twice⟩, ⟨edgeOther, input.compose other⟩] := rfl
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
def rejected : QFAbvStep reg reg := ⟨.boolLit false, input.update⟩
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
    (i : QFAbvStep Γinput Γ) (ρ : Env Γinput) (edge : SymbolicTransition Unit Γ)
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
