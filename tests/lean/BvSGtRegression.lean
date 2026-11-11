import Lean
import Ayxg.QfAbv.Eval
import Ayxg.QfAbv.ExecutableFP
import Ayxg.QfAbv.JsonCodec

open Lean Ayxg.QfAbv Ayxg.QfAbv.JsonCodec

local instance : FPInterpretation := FPInterpretation.executableChoice

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def checkCase [FPInterpretation] (j : Json) : Except String Unit := do
  let width ← natField j "width"
  let lhs ← natField j "lhs"
  let rhs ← natField j "rhs"
  let expected ← (← field j "result").getBool?
  let expression : Expr [] .bool :=
    Expr.bvSgt width (.bvLit width lhs) (.bvLit width rhs)
  let actual := Eval.eval (Γ := []) Env.nil expression
  unless actual == expected do
    throw s!"bvsgt case failed: width={width} lhs={lhs} rhs={rhs} expected={expected} actual={actual}"

#eval show IO Unit from do
  let contents ← IO.FS.readFile "tests/fixtures/bvsgt_cases.json"
  let fixture ← match Json.parse contents with
    | .ok value => pure value
    | .error message => throw (IO.userError s!"invalid bvsgt cases JSON: {message}")
  unless (← checked (field fixture "encoding" >>= Json.getStr?)) == "ayxg-bvsgt-cases-v1" do
    throw (IO.userError "unknown bvsgt shared-case encoding")
  unless (← checked (field fixture "resultDatatype" >>= Json.getStr?)) == "boolean" do
    throw (IO.userError "bvsgt shared-case result datatype must be boolean")
  let cases ← match (field fixture "cases" >>= Json.getArr?) with
    | .ok values => pure values
    | .error message => throw (IO.userError s!"invalid bvsgt cases array: {message}")
  if cases.isEmpty then
    throw (IO.userError "bvsgt shared cases must not be empty")
  for case in cases do
    match checkCase case with
    | .ok () => pure ()
    | .error message => throw (IO.userError message)
