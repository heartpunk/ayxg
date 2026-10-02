import LeanPy
import Ayxg.QfAbv.STS
open LeanPy Lean Ayxg.QfAbv
namespace Bridge

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
def natField (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
def sortOf (j : Json) : Except String TermSort := do
  match ← (← field j "kind").getStr? with
  | "bool" => return .bool
  | "bv" => return .bv (← natField j "width")
  | "array" => return .array (← natField j "index_width") (← natField j "value_width")
  | s => throw s!"unknown sort {s}"
def asSort {Γ : Ctx} (s : TermSort) : TypedExpr Γ → Except String (Expr Γ s)
  | .mk t e => if h : t = s then return h ▸ e else throw "sort mismatch"
def lookup (name : String) : (Γ : Ctx) → Except String (TypedExpr Γ)
  | [] => throw s!"unknown variable {name}"
  | d :: ds => do
    if d.name = name then return .mk d.sort (.var .here)
    let .mk s e ← lookup name ds
    match e with
    | .var v => return .mk s (.var (.there v))
    | _ => throw "invalid lookup"
def binOp : String → Option BvBinOp
  | "bv_add" => some .add | "bv_sub" => some .sub | "bv_mul" => some .mul
  | "bv_udiv" => some .udiv | "bv_urem" => some .urem | "bv_and" => some .and
  | "bv_or" => some .or | "bv_xor" => some .xor | "bv_shl" => some .shl
  | "bv_lshr" => some .lshr | "bv_ashr" => some .ashr | _ => none
partial def parseExpr (Γ : Ctx) (j : Json) : Except String (TypedExpr Γ) := do
  let op ← (← field j "op").getStr?
  let s ← sortOf (← field j "sort")
  let args := (j.getObjVal? "args" >>= Json.getArr?).toOption.getD #[]
  let arg (i : Nat) : Except String (TypedExpr Γ) := do
    let some a := args[i]? | throw "missing argument"
    parseExpr Γ a
  let a (i : Nat) (t : TermSort) : Except String (Expr Γ t) := do asSort t (← arg i)
  let node ← match op, s with
  | "var", _ => do lookup (← (← field j "name").getStr?) Γ
  | "bool_lit", .bool => do pure (.mk .bool (.boolLit (← (← field j "value").getBool?)))
  | "bv_lit", .bv w => do pure (.mk (.bv w) (.bvLit w (← natField j "value")))
  | "const_array", .array iw vw => do pure (.mk (.array iw vw) (.constArray iw vw (← a 0 (.bv vw))))
  | "bool_not", .bool => do pure (.mk .bool (.boolNot (← a 0 .bool)))
  | "bool_and", .bool => do pure (.mk .bool (.boolAnd (← a 0 .bool) (← a 1 .bool)))
  | "bool_or", .bool => do pure (.mk .bool (.boolOr (← a 0 .bool) (← a 1 .bool)))
  | "ite", _ => do pure (.mk s (.ite (← a 0 .bool) (← a 1 s) (← a 2 s)))
  | "bv_not", .bv w => do pure (.mk (.bv w) (.bvNot w (← a 0 (.bv w))))
  | "zero_extend", .bv _ | "sign_extend", .bv _ => do
    let .mk (.bv w) e ← arg 0 | throw "extension expects BV"
    let n ← natField j "amount"
    pure (.mk (.bv (w+n)) (if op == "zero_extend" then .zeroExt w n e else .signExt w n e))
  | "extract", .bv _ => do
    let .mk (.bv w) e ← arg 0 | throw "extract expects BV"
    let hi ← natField j "hi"
    let lo ← natField j "lo"
    if h : hi < w ∧ lo ≤ hi then
      let spec : ExtractSpec w := ⟨hi, lo, h.1, h.2⟩
      pure (.mk (.bv spec.width) (.extract spec e))
    else throw "invalid extraction bounds"
  | "concat", .bv _ => do
    let .mk (.bv wh) l ← arg 0 | throw "concat expects BV"
    let .mk (.bv wl) r ← arg 1 | throw "concat expects BV"
    pure (.mk (.bv (wh+wl)) (.concat wh wl l r))
  | "select", .bv _ => do
    let .mk (.array iw vw) m ← arg 0 | throw "select expects array"
    pure (.mk (.bv vw) (.select iw vw m (← a 1 (.bv iw))))
  | "store", .array iw vw => do
    pure (.mk (.array iw vw) (.store iw vw (← a 0 (.array iw vw)) (← a 1 (.bv iw)) (← a 2 (.bv vw))))
  | "eq", .bool => do
    match ← arg 0 with
    | .mk .bool l => pure (.mk .bool (.eqBool l (← a 1 .bool)))
    | .mk (.bv w) l => pure (.mk .bool (.eqBv w l (← a 1 (.bv w))))
    | _ => throw "array equality not admitted"
  | "bv_ult", .bool | "bv_ule", .bool | "bv_slt", .bool | "bv_sle", .bool => do
    let .mk (.bv w) l ← arg 0 | throw "comparison expects BV"
    let r ← a 1 (.bv w)
    let e := match op with
      | "bv_ult" => Expr.bvUlt w l r | "bv_ule" => Expr.bvUle w l r
      | "bv_slt" => Expr.bvSlt w l r | _ => Expr.bvSle w l r
    pure (.mk .bool e)
  | _, .bv w => do
    let some b := binOp op | throw s!"unknown BV operator {op}"
    pure (.mk (.bv w) (.bvBin b w (← a 0 (.bv w)) (← a 1 (.bv w))))
  | _, _ => throw s!"unknown operator {op}"
  return .mk s (← asSort s node)

def parseDecl (j : Json) : Except String Decl := do
  return ⟨← (← field j "name").getStr?, ← sortOf (← field j "sort")⟩
def parseValue (s : TermSort) (j : Json) : Except String (Denote s) := do
  match s with
  | .bool => j.getBool?
  | .bv w => return BitVec.ofNat w (← j.getNat?)
  | .array iw vw =>
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
def result (s : TermSort) (v : Denote s) : Except String Json := do
  let (kind, value) ← match s with
    | .bool => pure ("bool", toJson v)
    | .bv _ => pure ("bv", toJson v.toNat)
    | .array iw _ => do
      if iw > 8 then throw "array output limited to index width <=8"
      pure ("array", toJson ((List.range (2^iw)).map fun i => (v (BitVec.ofNat iw i)).toNat))
  return Json.mkObj [("kind", toJson kind), ("value", value)]
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

def request (j : Json) : Except String Json := do
  if (j.getObjVal? "mode" >>= Json.getStr?).toOption == some "transition" then
    return ← transitionRequest j
  let ds ← (← field j "declarations").getArr?
  let Γ ← ds.toList.mapM parseDecl
  let values ← (← field j "values").getArr?
  let env ← parseEnv Γ values.toList
  let .mk s e ← parseExpr Γ (← field j "expression")
  result s (Eval.eval env e)
end Bridge
@[python "py_eval_json"]
def evalJson (input : String) : String :=
  match Json.parse input >>= Bridge.request with
  | .ok output => output.compress
  | .error e => (Json.mkObj [("error", toJson e)]).compress
#export_python_registry "Bridge"
