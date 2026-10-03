import Bridge.Examples
import LeanPy
import Ayxg.QfAbv.STS
open LeanPy Lean Ayxg.QfAbv
namespace Bridge

/-- Test-only, explicitly chosen interpretation: canonical NaN bits, zero for
invalid casts and left operand sign for opposite-zero ties. Not a library default. -/
local instance fixtureFPInterpretation : FPInterpretation where
  nanBits _ x _ := x.rawBits
  nanBits_isNaN _ x h := by rw [FPValue.rawBits_roundtrip]; exact h
  invalidToBV _ _ _ _ _ := 0
  zeroTie _ _ leftNegative := leftNegative

def modeOf : String → Except String RoundingMode
  | "RNE" => pure .rne | "RNA" => pure .rna | "RTP" => pure .rtp
  | "RTN" => pure .rtn | "RTZ" => pure .rtz | _ => throw "invalid rounding mode"
def modeString : RoundingMode → String
  | .rne => "RNE" | .rna => "RNA" | .rtp => "RTP" | .rtn => "RTN" | .rtz => "RTZ"

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
def natField (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
def sortOf (j : Json) : Except String TermSort := do
  match ← (← field j "kind").getStr? with
  | "bool" => return .bool
  | "bv" => return .bv (← natField j "width")
  | "rm" => return .roundingMode
  | "fp" =>
    let eb ← natField j "exponent_bits"
    let sb ← natField j "significand_bits"
    if h : 2 ≤ eb ∧ 2 ≤ sb then return .fp ⟨eb, sb, h.1, h.2⟩
    else throw "invalid FP format"
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
  | "rm_lit", .roundingMode => do pure (.mk .roundingMode (.rmLit (← modeOf (← (← field j "value").getStr?))))
  | "bv_to_fp", .fp f => do pure (.mk (.fp f) (.fpFromBits f (← a 0 (.bv f.bitWidth))))
  | "fp_abs", .fp f | "fp_neg", .fp f => do
    pure (.mk (.fp f) (.fpUnary (if op == "fp_abs" then .abs else .neg) f (← a 0 (.fp f))))
  | "fp_rem", .fp f | "fp_min", .fp f | "fp_max", .fp f => do
    let o := if op == "fp_rem" then FpBinaryOp.rem else if op == "fp_min" then .min else .max
    pure (.mk (.fp f) (.fpBinary o f (← a 0 (.fp f)) (← a 1 (.fp f))))
  | "fp_add", .fp f | "fp_sub", .fp f | "fp_mul", .fp f | "fp_div", .fp f => do
    let o := if op == "fp_add" then FpRoundedOp.add else if op == "fp_sub" then .sub else if op == "fp_mul" then .mul else .div
    pure (.mk (.fp f) (.fpRounded o f (← a 0 .roundingMode) (← a 1 (.fp f)) (← a 2 (.fp f))))
  | "fp_fma", .fp f => do pure (.mk (.fp f) (.fpFma f (← a 0 .roundingMode) (← a 1 (.fp f)) (← a 2 (.fp f)) (← a 3 (.fp f))))
  | "fp_sqrt", .fp f => do pure (.mk (.fp f) (.fpSqrt f (← a 0 .roundingMode) (← a 1 (.fp f))))
  | "fp_round_to_integral", .fp f => do pure (.mk (.fp f) (.fpRoundToIntegral f (← a 0 .roundingMode) (← a 1 (.fp f))))
  | "fp_to_fp", .fp dst => do
    let .mk (.fp src) e ← arg 1 | throw "cast expects FP"
    pure (.mk (.fp dst) (.fpCast src dst (← a 0 .roundingMode) e))
  | "sbv_to_fp", .fp f | "ubv_to_fp", .fp f => do
    let .mk (.bv w) e ← arg 1 | throw "conversion expects BV"
    pure (.mk (.fp f) (.fpFromBv (op == "sbv_to_fp") w f (← a 0 .roundingMode) e))
  | "fp_to_sbv", .bv w | "fp_to_ubv", .bv w => do
    let .mk (.fp f) e ← arg 1 | throw "conversion expects FP"
    pure (.mk (.bv w) (.fpToBv (op == "fp_to_sbv") f w (← a 0 .roundingMode) e))
  | "fp_to_ieee_bv", .bv _ => do
    let .mk (.fp f) e ← arg 0 | throw "bit transport expects FP"
    pure (.mk (.bv f.bitWidth) (.fpToBits f e))
  | "fp_eq", .bool | "fp_lt", .bool | "fp_le", .bool | "fp_gt", .bool | "fp_ge", .bool => do
    let .mk (.fp f) e ← arg 0 | throw "comparison expects FP"
    let o := if op == "fp_eq" then FpCompareOp.eq else if op == "fp_lt" then .lt else if op == "fp_le" then .le else if op == "fp_gt" then .gt else .ge
    pure (.mk .bool (.fpCompare o f e (← a 1 (.fp f))))
  | "fp_is_normal", .bool | "fp_is_subnormal", .bool | "fp_is_zero", .bool | "fp_is_infinite", .bool | "fp_is_nan", .bool | "fp_is_negative", .bool | "fp_is_positive", .bool => do
    let .mk (.fp f) e ← arg 0 | throw "classification expects FP"
    let o := if op == "fp_is_normal" then FpClassifyOp.normal else if op == "fp_is_subnormal" then .subnormal else if op == "fp_is_zero" then .zero else if op == "fp_is_infinite" then .infinite else if op == "fp_is_nan" then .nan else if op == "fp_is_negative" then .negative else .positive
    pure (.mk .bool (.fpClassify o f e))
  | "fp_construct", .fp f => do
    let sign ← a 0 (.bv 1)
    let exp ← a 1 (.bv f.exponentBits)
    let frac ← a 2 (.bv (f.significandBits - 1))
    let bits := Expr.concat 1 (f.exponentBits + (f.significandBits - 1)) sign
      (.concat f.exponentBits (f.significandBits - 1) exp frac)
    have h : 1 + (f.exponentBits + (f.significandBits - 1)) = f.bitWidth := by
      unfold FPFormat.bitWidth; have := f.significand_ge_two; omega
    pure (.mk (.fp f) (.fpFromBits f (h ▸ bits)))
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
    | .mk (.fp f) l => pure (.mk .bool (.eqFp f l (← a 1 (.fp f))))
    | .mk .roundingMode l => pure (.mk .bool (.eqRoundingMode l (← a 1 .roundingMode)))
    | .mk .bool l => pure (.mk .bool (.eqBool l (← a 1 .bool)))
    | .mk (.bv w) l => pure (.mk .bool (.eqBv w l (← a 1 (.bv w))))
    | .mk (.array iw vw) l => pure (.mk .bool (.eqArray iw vw l (← a 1 (.array iw vw))))
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

def request (j : Json) : Except String Json := do
  if (j.getObjVal? "mode" >>= Json.getStr?).toOption == some "segment" then
    return ← segmentRequest j
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
