import Bridge.Examples
import LeanPy
import Ayxg.QfAbv.STS
import Ayxg.QfAbv.JsonCodec
open LeanPy Lean Ayxg.QfAbv
namespace Bridge

/-- Test-only, explicitly chosen interpretation: canonical NaN bits, zero for
invalid casts and left operand sign for opposite-zero ties. Not a library default. -/
local instance fixtureFPInterpretation : FPInterpretation where
  nanBits _ x _ := x.rawBits
  nanBits_isNaN _ x h := by rw [FPValue.rawBits_roundtrip]; exact h
  invalidToBV _ _ _ _ _ := 0
  zeroTie _ _ leftNegative := leftNegative

open Ayxg.QfAbv.JsonCodec

def parseValue : (s : TermSort) → Json → Except String (Denote s)
  | .fp f, j => do return FPValue.ofBits f (BitVec.ofNat f.bitWidth (← j.getNat?))
  | .roundingMode, j => do modeOf (← j.getStr?)
  | .bool, j => j.getBool?
  | .bv w, j => do return BitVec.ofNat w (← j.getNat?)
  | .array iw vw, j => do
    let d ← natField j "default"
    let entries ← (← field j "entries").getArr?
    let mut mem : Mem iw vw := Eval.memConst (BitVec.ofNat vw d)
    for item in entries do
      let pair ← item.getArr?
      let some idx := pair[0]? | throw "missing array index"
      let some val := pair[1]? | throw "missing array value"
      mem := Eval.memStore mem (BitVec.ofNat iw (← idx.getNat?)) (BitVec.ofNat vw (← val.getNat?))
    return mem
def parseEnv : (Γ : Ctx) → List Json → Except String (Env Γ)
  | [], [] => pure .nil
  | d :: ds, v :: vs => do pure (.cons (← parseValue d.sort v) (← parseEnv ds vs))
  | _, _ => throw "valuation length mismatch"
def resultJson (kind : String) (value : Json) : Json :=
  Json.mkObj [("kind", toJson kind), ("value", value)]
def result : (s : TermSort) → Denote s → Except String Json
  | .fp _, v => pure (resultJson "fp" (toJson v.model.toNatBits))
  | .roundingMode, v => pure (resultJson "rm" (toJson (modeString v)))
  | .bool, v => pure (resultJson "bool" (toJson v))
  | .bv _, v => pure (resultJson "bv" (toJson v.toNat))
  | .array iw _, v => do
    if iw > 8 then throw "array output limited to index width <=8"
    pure (resultJson "array" (toJson ((List.range (2^iw)).map fun i => (v (BitVec.ofNat iw i)).toNat)))
def parseContext (j : Json) : Except String Ctx := do
  (← j.getArr?).toList.mapM parseDecl

def parseUpdate (Γ : Ctx) : (Δ : Ctx) → List Json → Except String (StateUpdate Γ Δ)
  | [], [] => pure .nil
  | d :: ds, e :: es => do
    pure (.cons (← asSort d.sort (← parseExpr Γ e)) (← parseUpdate Γ ds es))
  | _, _ => throw "update length mismatch"

def parseStep (Γ Δ : Ctx) (j : Json) : Except String (QFAbvStep Γ Δ) := do
  return ⟨← asSort .bool (← parseExpr Γ (← field j "guard")),
    ← parseUpdate Γ Δ (← (← field j "rhs").getArr?).toList⟩

def envResult : {Γ : Ctx} → Env Γ → Except String (List Json)
  | [], .nil => pure []
  | d :: _, .cons head tail => do
    return (← result d.sort head) :: (← envResult tail)

def runStep {Γ Δ : Ctx} (step : QFAbvStep Γ Δ) (env : Env Γ) : Except String Json := do
  if Eval.evalBool env step.guard then
    return toJson (← envResult (step.update.eval env))
  else return Json.null

def transitionRequest (j : Json) : Except String Json := do
  let Γ ← parseContext (← field j "declarations")
  let env ← parseEnv Γ (← (← field j "values").getArr?).toList
  let Δ ← parseContext (← field j "middle")
  let Ω ← parseContext (← field j "output")
  let left ← parseStep Γ Δ (← field j "left")
  let right ← parseStep Δ Ω (← field j "right")
  let sequential ← if Eval.evalBool env left.guard then
    runStep right (left.update.eval env) else pure Json.null
  return Json.mkObj [
    ("update", toJson (← envResult (left.update.eval env))),
    ("update_composed", toJson (← envResult ((left.update.compose right.update).eval env))),
    ("update_sequential", toJson (← envResult (right.update.eval (left.update.eval env)))),
    ("step", ← runStep left env),
    ("composed", ← runStep (left.compose right) env),
    ("sequential", sequential),
    ("identity_update", toJson (← envResult ((StateUpdate.identity Γ).eval env))),
    ("identity_step", ← runStep (QFAbvStep.identity Γ) env),
    ("identity_left", ← runStep ((QFAbvStep.identity Γ).compose left) env),
    ("identity_right", ← runStep (left.compose (QFAbvStep.identity Δ)) env)]

def segmentOutputs {Γ Δ Ω : Ctx} (segment : QFAbvSegment Γ Δ Ω)
    (env : Env Γ) (fuel : Nat) : Except String (List Json) := do
  let entry := segment.input.label
  if !Eval.evalBool env entry.guard then return []
  let mut frontier := [entry.update.eval env]
  let mut outputs := []
  for _ in List.range (fuel + 1) do
    for state in frontier do
      for exit in segment.exits do
        if Eval.evalBool state exit.label.guard then
          outputs := toJson (← envResult (exit.label.update.eval state)) :: outputs
    frontier := frontier.flatMap fun state => segment.body.steps.filterMap fun step =>
      if Eval.evalBool state step.guard then some (step.update.eval state) else none
  return outputs

def segmentRequest (j : Json) : Except String Json := do
  let Γ ← parseContext (← field j "declarations")
  let Δ ← parseContext (← field j "body_context")
  let Ω ← parseContext (← field j "output")
  let env ← parseEnv Γ (← (← field j "values").getArr?).toList
  let entry ← parseStep Γ Δ (← field j "entry")
  let steps ← (← (← field j "steps").getArr?).toList.mapM (parseStep Δ Δ)
  let exits ← (← (← field j "exits").getArr?).toList.mapM (parseStep Δ Ω)
  let segment : QFAbvSegment Γ Δ Ω := ⟨⟨entry⟩, ⟨steps⟩, exits.map (fun s => ⟨s⟩)⟩
  let fuel ← natField j "fuel"
  if fuel > 3 then throw "segment exploration limited to 0..3 transitions"
  let nodes : List (Ayxg.SegmentNode Nat (QFAbvSegment Γ Δ Ω)) :=
    [⟨0, segment, []⟩, ⟨1, segment, [0]⟩, ⟨2, segment, [0]⟩]
  let dag : Ayxg.SegmentDAG Nat (QFAbvSegment Γ Δ Ω) := {
    nodes := nodes, roots := [1,2]
    ordered := by simp [nodes, Ayxg.SegmentNode.Ordered]
    rootsPresent := by
      intro root h
      simp at h
      rcases h with rfl | rfl
      · exact ⟨⟨1, segment, [0]⟩, by simp [nodes], rfl⟩
      · exact ⟨⟨2, segment, [0]⟩, by simp [nodes], rfl⟩ }
  let mut shared := []
  for parent in dag.nodes.drop 1 do
    for key in parent.children do
      let some child := dag.nodes.find? (fun n => n.key == key) | throw "missing DAG child"
      shared := toJson (← segmentOutputs child.segment env fuel) :: shared
  return Json.mkObj [("direct", toJson (← segmentOutputs segment env fuel)),
    ("shared", toJson shared)]

def innermost (s : TermSort) : Expr [⟨"x", s⟩] s := .var .here

/-- Test-only fixture: the same runtime variable object at two valid sorts. -/
private unsafe def writerPolymorphicShared : Json :=
  let vb := innermost .bool
  let vv : Expr [⟨"x", .bv 8⟩] (.bv 8) := unsafeCast vb
  let b : Expr [] .bool := .letPar (.cons "x" .bool (.boolLit true) .nil) vb
  let v : Expr [] (.bv 8) := .letPar (.cons "x" (.bv 8) (.bvLit 8 7) .nil) vv
  writeRootsDag [.mk .bool b, .mk (.bv 8) v]

@[implemented_by writerPolymorphicShared]
def writerPolymorphic : Json :=
  let b : Expr [] .bool := .letPar (.cons "x" .bool (.boolLit true) .nil) (innermost .bool)
  let v : Expr [] (.bv 8) := .letPar (.cons "x" (.bv 8) (.bvLit 8 7) .nil) (innermost (.bv 8))
  writeRootsDag [.mk .bool b, .mk (.bv 8) v]

def request (j : Json) : Except String Json := do
  if (j.getObjVal? "mode" >>= Json.getStr?).toOption == some "writer_polymorphic" then
    return writerPolymorphic
  if (j.getObjVal? "mode" >>= Json.getStr?).toOption == some "segment" then
    return ← segmentRequest j
  if (j.getObjVal? "mode" >>= Json.getStr?).toOption == some "transition" then
    return ← transitionRequest j
  let ds ← (← field j "declarations").getArr?
  let Γ ← ds.toList.mapM parseDecl
  if (j.getObjVal? "mode" >>= Json.getStr?).toOption == some "roundtrip" then
    return writeRootsDag (← parseRootsDag Γ (← field j "expression_dag"))
  let values ← (← field j "values").getArr?
  let env ← parseEnv Γ values.toList
  let expression ← match (j.getObjVal? "expression_dag").toOption with
    | none => parseExpr Γ (← field j "expression")
    | some dag => do
      let [term] ← parseRootsDag Γ dag | throw "expected one expression root"
      pure term
  let .mk s e := expression
  result s (Eval.eval env e)
end Bridge
@[python "py_eval_json"]
def evalJson (input : String) : String :=
  match Json.parse input >>= Bridge.request with
  | .ok output => output.compress
  | .error e => (Json.mkObj [("error", toJson e)]).compress
#export_python_registry "Bridge"
