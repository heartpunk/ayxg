import Ayxg.QfAbv.Eval
import Ayxg.QfAbv.JsonCodec

open Lean Ayxg.QfAbv Ayxg.QfAbv.JsonCodec

-- Kernel-checked examples exercise the public evaluator with an arbitrary FP
-- interpretation: integer arithmetic must not depend on floating-point choices.
private def divide [FPInterpretation] (w a b : Nat) : BitVec w :=
  Eval.eval (Γ := []) .nil (.bvBin .sdiv w (.bvLit w a) (.bvLit w b))

private theorem divide_eq [FPInterpretation] (w a b : Nat) :
    divide w a b = BitVec.smtSDiv (BitVec.ofNat w a) (BitVec.ofNat w b) := rfl

example [FPInterpretation] : divide 8 7 3 = 2 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 249 3 = 254 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 7 253 = 254 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 249 253 = 2 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 0 0 = 255 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 7 0 = 255 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 249 0 = 1 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 8 128 255 = 128 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 1 0 0 = 1 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 1 1 0 = 1 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] : divide 1 1 1 = 1 := by rw [divide_eq]; decide +kernel
example [FPInterpretation] :
    divide 64 18446744073709551609 3 = 18446744073709551614 := by rw [divide_eq]; decide +kernel

-- Check both codec directions with literal operator spelling, so swapping the
-- parser and writer to an unsigned operator cannot hide behind a round trip.
#eval show IO Unit from do
  unless binOp "bv_sdiv" == some .sdiv do
    throw (IO.userError "bv_sdiv must parse as signed division")
  let term : Expr [] (.bv 8) := .bvBin .sdiv 8 (.bvLit 8 249) (.bvLit 8 3)
  let encoded := writeRootsDag [.mk (.bv 8) term]
  let checked : Except String Unit := do
    let nodes ← (← field encoded "nodes").getArr?
    let some root := nodes.back? | throw "empty encoded DAG"
    unless (← (← field root "op").getStr?) == "bv_sdiv" do
      throw "signed division serialized with the wrong operator"
    match ← parseRootsDag [] encoded with
    | [.mk (.bv 8) (.bvBin .sdiv 8 (.bvLit 8 249) (.bvLit 8 3))] => pure ()
    | _ => throw "signed division failed to round trip"
  match checked with
  | .ok () => pure ()
  | .error message => throw (IO.userError message)
