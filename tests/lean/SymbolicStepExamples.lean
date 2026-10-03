import Ayxg.QfAbv.SymbolicStep

namespace Ayxg.QfAbv.SymbolicStepExamples

def reg : Ctx := [⟨"x", .bv 8⟩]
def input : QFAbvStep reg reg :=
  ⟨.boolLit true, .cons (.bvBin .add 8 (.var .here) (.bvLit 8 1)) .nil⟩
def twice : QFAbvStep reg reg :=
  ⟨.eqBv 8 (.var .here) (.bvLit 8 4),
   .cons (.bvBin .mul 8 (.var .here) (.bvLit 8 2)) .nil⟩
def other : QFAbvStep reg reg :=
  ⟨.boolNot (.eqBv 8 (.var .here) (.bvLit 8 4)),
   .cons (.bvLit 8 99) .nil⟩
def model : QFAbvSTS reg := ⟨[twice, other]⟩
def first : QFAbvStep reg reg :=
  (model.symbolicStep input).headD (QFAbvStep.identity reg)
def second : QFAbvStep reg reg :=
  (model.symbolicStep input).getD 1 (QFAbvStep.identity reg)

-- Actual returned family retains source edge order and both branches.
example : model.symbolicStep input = [input.compose twice, input.compose other] := rfl
example : (model.symbolicStep input).length = 2 := rfl
example : (⟨[]⟩ : QFAbvSTS reg).symbolicStep input = [] := rfl

variable [FPInterpretation]

-- Composition is (x + 1) * 2 = 8, not x * 2 + 1 = 7.
example : Env.lookup (first.update.eval (.cons (3 : BitVec 8) .nil)) .here = (8 : BitVec 8) := rfl
-- Guard tests updated x = 4, rather than original x = 4.
example : Eval.evalBool (.cons (3 : BitVec 8) .nil) first.guard = true := rfl
example : Eval.evalBool (.cons (4 : BitVec 8) .nil) first.guard = false := rfl
example : Eval.evalBool (.cons (3 : BitVec 8) .nil) second.guard = false := rfl
example : Eval.evalBool (.cons (4 : BitVec 8) .nil) second.guard = true := rfl
example : Env.lookup (second.update.eval (.cons (4 : BitVec 8) .nil)) .here = (99 : BitVec 8) := rfl

-- Input rejection remains rejection even when the edge itself is enabled.
def rejected : QFAbvStep reg reg := ⟨.boolLit false, input.update⟩
example : Eval.evalBool (.cons (3 : BitVec 8) .nil)
    ((model.symbolicStep rejected).headD input).guard = false := rfl

-- Empty source STS has no concrete transition; no solver assumption is needed.
example (ρ : Env reg) (t : Env reg) :
    ¬ (∃ successor ∈ (⟨[]⟩ : QFAbvSTS reg).symbolicStep input,
      successor.denotes ρ t) := by
  simp [QFAbvSTS.symbolicStep, ShareCommon.shareCommon']

-- Memory arrays remain supported through the same generic theorem.
example {Γinput Γ : Ctx} (m : QFAbvSTS Γ) (i : QFAbvStep Γinput Γ)
    (ρ : Env Γinput) (t : Env Γ) (h : Eval.evalBool ρ i.guard = true)
    (step : m.toLTS.canStep (i.update.eval ρ) t) :
    ∃ o ∈ m.symbolicStep i, o.denotes ρ t :=
  QFAbvSTS.symbolicStep_complete m i ρ t h step

-- Runtime-only allocation check, not a proof mechanism: hash-consed equal
-- outputs share an object. Semantic proofs do not depend on pointer equality.
unsafe def checkSharing : IO Unit := do
  let outputs := (⟨[twice, twice]⟩ : QFAbvSTS reg).symbolicStep input
  match outputs with
  | a :: b :: [] =>
      if ptrAddrUnsafe a == ptrAddrUnsafe b then
        IO.println "shared successor object: PASS"
      else throw (IO.userError "equal successors were not shared")
  | _ => throw (IO.userError "wrong successor count")

#eval checkSharing

end Ayxg.QfAbv.SymbolicStepExamples
