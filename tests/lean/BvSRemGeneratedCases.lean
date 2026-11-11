import Ayxg.QfAbv.Eval
import Ayxg.QfAbv.JsonCodec

open Lean Ayxg.QfAbv Ayxg.QfAbv.JsonCodec

local instance pbtFPInterpretation : FPInterpretation where
  nanBits _ x _ := x.rawBits
  nanBits_isNaN _ x h := by rw [FPValue.rawBits_roundtrip]; exact h
  invalidToBV _ _ _ _ _ := 0
  zeroTie _ _ leftNegative := leftNegative

#eval show IO Unit from do
  let path ← match (← IO.getEnv "AYXG_BVSREM_PBT_CASES") with
    | some value => pure value
    | none => throw (IO.userError "missing AYXG_BVSREM_PBT_CASES")
  let source ← IO.FS.readFile path
  let input ← match Json.parse source with
    | .ok json => pure json
    | .error message => throw (IO.userError message)
  let operator ← match (field input "operator" >>= Json.getStr?).toOption with
    | some value => pure value
    | none => throw (IO.userError "missing bvsrem operator")
  unless operator == "bv_srem" do
    throw (IO.userError "property cases must use bv_srem")
  let cases ← match (field input "cases" >>= Json.getArr?).toOption with
    | some values => pure values
    | none => throw (IO.userError "missing bvsrem cases")
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
    unless width > 0 && left < 2 ^ width && right < 2 ^ width do
      throw (IO.userError "bvsrem case operands must fit a positive bit-vector width")
    let sort := Json.mkObj [("kind", toJson "bv"), ("width", toJson width)]
    let literal (value : Nat) := Json.mkObj [
      ("op", toJson "bv_lit"), ("sort", sort), ("value", toJson value)]
    let expression := Json.mkObj [
      ("op", toJson operator), ("sort", sort),
      ("args", toJson #[literal left, literal right])]
    let .ok (.mk (.bv w) term) := parseExpr [] expression
      | throw (IO.userError "failed to parse generated bvsrem expression")
    let actual := (Eval.eval (Γ := []) .nil term).toNat
    unless actual == expected do
      throw (IO.userError s!"Lean bvsrem mismatch at width {width}: {left}, {right} => {actual}, expected {expected}")
