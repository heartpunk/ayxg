import Ayxg.QfAbv.Eval
import Ayxg.QfAbv.JsonCodec

open Lean Ayxg.QfAbv Ayxg.QfAbv.JsonCodec

-- The fixture tests integer bit-vector behavior only; this explicit instance
-- gives the otherwise irrelevant floating-point choices concrete values.
local instance fixtureFPInterpretation : FPInterpretation where
  nanBits _ x _ := x.rawBits
  nanBits_isNaN _ x h := by rw [FPValue.rawBits_roundtrip]; exact h
  invalidToBV _ _ _ _ _ := 0
  zeroTie _ _ leftNegative := leftNegative

private def remainder (w a b : Nat) : BitVec w :=
  Eval.eval (Γ := []) .nil (.bvBin .srem w (.bvLit w a) (.bvLit w b))

private theorem remainder_eq (w a b : Nat) :
    remainder w a b = (BitVec.ofNat w a).srem (BitVec.ofNat w b) := rfl

example : remainder 8 249 3 = 255 := by rw [remainder_eq]; decide +kernel
example : remainder 8 7 253 = 1 := by rw [remainder_eq]; decide +kernel
example : remainder 8 249 253 = 255 := by rw [remainder_eq]; decide +kernel
example : remainder 8 7 0 = 7 := by rw [remainder_eq]; decide +kernel
example : remainder 8 128 255 = 0 := by rw [remainder_eq]; decide +kernel
example : remainder 64 18446744073709551609 3 = 18446744073709551615 := by
  rw [remainder_eq]; decide +kernel

-- The checked-in vectors are shared with Python and Z3. This exercises the
-- JSON parser, evaluator, writer, and parser again using the canonical spelling.
#eval show IO Unit from do
  let source ← IO.FS.readFile "tests/fixtures/bvsrem.json"
  let input ← match Json.parse source with
    | .ok json => pure json
    | .error message => throw (IO.userError message)
  let operator ← match (field input "operator" >>= Json.getStr?).toOption with
    | some value => pure value
    | none => throw (IO.userError "missing bvsrem operator")
  unless operator == "bv_srem" do
    throw (IO.userError "fixture operator must be bv_srem")
  let cases ← match (field input "cases" >>= Json.getArr?).toOption with
    | some values => pure values
    | none => throw (IO.userError "missing bvsrem cases")
  unless binOp operator == some .srem do
    throw (IO.userError "bv_srem must parse as signed remainder")
  for item in cases do
    let width ← match natField item "width" with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    let left ← match natField item "left" with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    let right ← match natField item "right" with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    let expected ← match natField item "expected" with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    let sort := Json.mkObj [("kind", toJson "bv"), ("width", toJson width)]
    let literal (value : Nat) := Json.mkObj [
      ("op", toJson "bv_lit"), ("sort", sort), ("value", toJson value)]
    let expression := Json.mkObj [
      ("op", toJson operator), ("sort", sort),
      ("args", toJson #[literal left, literal right])]
    let .ok (.mk (.bv w) term) := parseExpr [] expression
      | throw (IO.userError "failed to parse bvsrem fixture expression")
    let actual := (Eval.eval (Γ := []) .nil term).toNat
    unless actual == expected do
      throw (IO.userError s!"bvsrem mismatch at width {width}: {left}, {right} => {actual}, expected {expected}")
    let encoded := writeRootsDag [.mk (.bv w) term]
    match parseRootsDag [] encoded with
    | .ok [.mk (.bv _) (.bvBin .srem _ (.bvLit _ encodedLeft) (.bvLit _ encodedRight))] =>
      unless encodedLeft == left && encodedRight == right do
        throw (IO.userError "bv_srem failed to round trip through the Lean DAG codec")
    | _ => throw (IO.userError "failed to decode bvsrem Lean DAG")
