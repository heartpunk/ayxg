import Lean
import Ayxg.QfAbv.Step

namespace Ayxg.QfAbv.JsonCodec
open Lean

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
def lookupIndex : Nat → (Γ : Ctx) → Except String (TypedExpr Γ)
  | _, [] => throw "variable position outside context"
  | 0, d :: _ => return .mk d.sort (.var .here)
  | n + 1, _ :: ds => do
    let .mk s e ← lookupIndex n ds
    match e with
    | .var v => return .mk s (.var (.there v))
    | _ => throw "invalid positional lookup"

def binOp : String → Option BvBinOp
  | "bv_add" => some .add | "bv_sub" => some .sub | "bv_mul" => some .mul
  | "bv_udiv" => some .udiv | "bv_sdiv" => some .sdiv | "bv_urem" => some .urem
  | "bv_srem" => some .srem | "bv_and" => some .and
  | "bv_or" => some .or | "bv_xor" => some .xor | "bv_shl" => some .shl
  | "bv_lshr" => some .lshr | "bv_ashr" => some .ashr | _ => none
def parseBindingsWith {m : Type → Type} [Monad m] [MonadExceptOf String m]
    [MonadLiftT (Except String) m]
    (recurse : (Γ : Ctx) → Json → m (TypedExpr Γ))
    (Γ : Ctx) : List Json → List Json → m (Σ Δ, Bindings Γ Δ)
  | [], [] => return ⟨Γ, .nil⟩
  | d :: ds, rhs :: rest => do
    let name ← (← field d "name").getStr?
    let sort ← sortOf (← field d "sort")
    let value ← asSort sort (← recurse Γ rhs)
    let ⟨Δ, bindings⟩ ← parseBindingsWith recurse Γ ds rest
    return ⟨{ name := name, sort := sort } :: Δ, .cons name sort value bindings⟩
  | _, _ => throw "binding count mismatch"

def parseNode {m : Type → Type} [Monad m] [MonadExceptOf String m]
    [MonadLiftT (Except String) m]
    (recurse : (Γ : Ctx) → Json → m (TypedExpr Γ))
    (Γ : Ctx) (j : Json) : m (TypedExpr Γ) := do
  let op ← (← field j "op").getStr?
  let s ← sortOf (← field j "sort")
  let args := (j.getObjVal? "args" >>= Json.getArr?).toOption.getD #[]
  let arg (i : Nat) : m (TypedExpr Γ) := do
    let some a := args[i]? | throw "missing argument"
    recurse Γ a
  let a (i : Nat) (t : TermSort) : m (Expr Γ t) := do asSort t (← arg i)
  let node ← match op, s with
  | "var", _ => do
    match (j.getObjVal? "index").toOption with
    | some index => lookupIndex (← index.getNat?) Γ
    | none => lookup (← (← field j "name").getStr?) Γ
  | "let_par", _ => do
    let declarations ← (← field j "bindings").getArr?
    if args.size != declarations.size + 1 then throw "let_par arity mismatch"
    let ⟨Δ, bindings⟩ ← parseBindingsWith recurse Γ declarations.toList (args.toList.take declarations.size)
    let body ← asSort s (← recurse Δ args[declarations.size]!)
    return .mk s (.letPar bindings body)
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


partial def parseExpr (Γ : Ctx) (j : Json) : Except String (TypedExpr Γ) :=
  parseNode parseExpr Γ j

def parseDecl (j : Json) : Except String Decl := do
  return ⟨← (← field j "name").getStr?, ← sortOf (← field j "sort")⟩

/-- Each node is memoized separately for each declaration context. A shared
variable body can therefore be used under different lexical binders safely. -/
abbrev DagCache := Std.HashMap Nat (List (Σ Γ, TypedExpr Γ))

partial def parseDagAt (nodes : Array Json) (Γ : Ctx) (index : Nat) :
    StateT DagCache (Except String) (TypedExpr Γ) := do
  for ⟨Δ, term⟩ in (← get).getD index [] do
    if h : Δ = Γ then return h ▸ term
  let some node := nodes[index]? | throw "DAG node index outside array"
  let args ← (← field node "args").getArr?
  for child in args do
    if (← child.getNat?) ≥ index then throw "DAG children must precede parent"
  let term ← parseNode (fun Δ child => do parseDagAt nodes Δ (← child.getNat?)) Γ node
  modify fun cache => cache.insert index (⟨Γ, term⟩ :: cache.getD index [])
  return term

/-- Read the same canonical typed-expr-roots-dag-v1 used by Python. Bindings
remain bindings; no tree expansion or let elimination occurs. -/
def parseRootsDag (Γ : Ctx) (j : Json) : Except String (List (TypedExpr Γ)) := do
  if (← (← field j "encoding").getStr?) != "typed-expr-roots-dag-v1" then
    throw "unknown expression DAG encoding"
  let nodes ← (← field j "nodes").getArr?
  let roots ← (← field j "roots").getArr?
  let action : StateT DagCache (Except String) (List (TypedExpr Γ)) :=
    roots.toList.mapM fun (root : Json) => do
      let index ← root.getNat?
      parseDagAt nodes Γ index
  action.run' {}

def sortJson : TermSort → Json
  | .bool => Json.mkObj [("kind", toJson "bool")]
  | .bv w => Json.mkObj [("kind", toJson "bv"), ("width", toJson w)]
  | .array i v => Json.mkObj [("kind", toJson "array"), ("index_width", toJson i), ("value_width", toJson v)]
  | .roundingMode => Json.mkObj [("kind", toJson "rm")]
  | .fp f => Json.mkObj [("kind", toJson "fp"), ("exponent_bits", toJson f.exponentBits), ("significand_bits", toJson f.significandBits)]

def varIndex : Var Γ s → Nat
  | .here => 0
  | .there v => varIndex v + 1

structure Writer where
  nodes : Array Json := #[]
  interned : Std.HashMap String Nat := {}
  visited : Std.HashMap (USize × String) Nat := {}
  /-- Retain input objects until serialization ends, preventing address reuse. -/
  retained : List (Σ Γ, TypedExpr Γ) := []

/-- Intern by shallow record (child indices, never expanded child trees). -/
def emit (s : TermSort) (op : String) (args : List Nat := [])
    (fields : List (String × Json) := []) : StateM Writer Nat := do
  let node := Json.mkObj ([("op", toJson op), ("sort", sortJson s), ("args", toJson args)] ++ fields)
  let key := node.compress
  let state ← get
  if let some index := state.interned[key]? then return index
  let index := state.nodes.size
  set { state with nodes := state.nodes.push node, interned := state.interned.insert key index }
  return index

private abbrev NodeKey := {Γ : Ctx} → {s : TermSort} → Expr Γ s → Option USize

mutual
private partial def writeExprWith {Γ : Ctx} {s : TermSort} (keyOf : NodeKey) (e : Expr Γ s) : StateM Writer Nat := do
  let address := (keyOf e).map fun address => (address, (sortJson s).compress)
  if let some address := address then
    if let some index := (← get).visited[address]? then return index
  let index ← match s, e with
  | _, .var v => emit s "var" [] [("index", toJson (varIndex v))]
  | _, .boolLit b => emit s "bool_lit" [] [("value", toJson b)]
  | _, .bvLit w v => emit s "bv_lit" [] [("value", toJson (v % 2^w))]
  | _, .rmLit r => emit s "rm_lit" [] [("value", toJson (modeString r))]
  | _, .letPar bs body => do
    let (decls, rhs) ← writeBindingsWith keyOf bs
    emit s "let_par" (rhs ++ [← writeExprWith keyOf body]) [("bindings", toJson decls)]
  | _, .fpFromBits _ a => emit s "bv_to_fp" [← writeExprWith keyOf a]
  | _, .fpToBits _ a => emit s "fp_to_ieee_bv" [← writeExprWith keyOf a]
  | _, .fpFma _ r a b c => emit s "fp_fma" [← writeExprWith keyOf r, ← writeExprWith keyOf a, ← writeExprWith keyOf b, ← writeExprWith keyOf c]
  | _, .fpSqrt _ r a => emit s "fp_sqrt" [← writeExprWith keyOf r, ← writeExprWith keyOf a]
  | _, .fpRoundToIntegral _ r a => emit s "fp_round_to_integral" [← writeExprWith keyOf r, ← writeExprWith keyOf a]
  | _, .fpCast _ _ r a => emit s "fp_to_fp" [← writeExprWith keyOf r, ← writeExprWith keyOf a]
  | _, .eqFp _ a b => emit s "eq" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .eqRoundingMode a b => emit s "eq" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .constArray _ _ a => emit s "const_array" [← writeExprWith keyOf a]
  | _, .boolNot a => emit s "bool_not" [← writeExprWith keyOf a]
  | _, .boolAnd a b => emit s "bool_and" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .boolOr a b => emit s "bool_or" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .ite a b c => emit s "ite" [← writeExprWith keyOf a, ← writeExprWith keyOf b, ← writeExprWith keyOf c]
  | _, .bvNot _ a => emit s "bv_not" [← writeExprWith keyOf a]
  | _, .concat _ _ a b => emit s "concat" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .select _ _ a b => emit s "select" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .store _ _ a b c => emit s "store" [← writeExprWith keyOf a, ← writeExprWith keyOf b, ← writeExprWith keyOf c]
  | _, .bvUlt _ a b => emit s "bv_ult" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .bvUle _ a b => emit s "bv_ule" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .bvSlt _ a b => emit s "bv_slt" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .bvSle _ a b => emit s "bv_sle" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .eqBool a b => emit s "eq" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .eqBv _ a b => emit s "eq" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .eqArray _ _ a b => emit s "eq" [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .bvBin o _ a b =>
    let op := match o with
      | .add => "bv_add"
      | .sub => "bv_sub"
      | .mul => "bv_mul"
      | .udiv => "bv_udiv"
      | .sdiv => "bv_sdiv"
      | .urem => "bv_urem"
      | .srem => "bv_srem"
      | .and => "bv_and"
      | .or => "bv_or"
      | .xor => "bv_xor"
      | .shl => "bv_shl"
      | .lshr => "bv_lshr"
      | .ashr => "bv_ashr"
    emit s op [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .fpUnary o _ a =>
    let op := match o with
      | .abs => "fp_abs"
      | .neg => "fp_neg"
    emit s op [← writeExprWith keyOf a]
  | _, .fpBinary o _ a b =>
    let op := match o with
      | .rem => "fp_rem"
      | .min => "fp_min"
      | .max => "fp_max"
    emit s op [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .fpRounded o _ r a b =>
    let op := match o with
      | .add => "fp_add"
      | .sub => "fp_sub"
      | .mul => "fp_mul"
      | .div => "fp_div"
    emit s op [← writeExprWith keyOf r, ← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .fpCompare o _ a b =>
    let op := match o with
      | .eq => "fp_eq"
      | .lt => "fp_lt"
      | .le => "fp_le"
      | .gt => "fp_gt"
      | .ge => "fp_ge"
    emit s op [← writeExprWith keyOf a, ← writeExprWith keyOf b]
  | _, .fpClassify o _ a =>
    let op := match o with
      | .normal => "fp_is_normal"
      | .subnormal => "fp_is_subnormal"
      | .zero => "fp_is_zero"
      | .infinite => "fp_is_infinite"
      | .nan => "fp_is_nan"
      | .negative => "fp_is_negative"
      | .positive => "fp_is_positive"
    emit s op [← writeExprWith keyOf a]
  | _, .fpToBv signed _ _ r a => emit s (if signed then "fp_to_sbv" else "fp_to_ubv") [← writeExprWith keyOf r, ← writeExprWith keyOf a]
  | _, .fpFromBv signed _ _ r a => emit s (if signed then "sbv_to_fp" else "ubv_to_fp") [← writeExprWith keyOf r, ← writeExprWith keyOf a]
  | _, .zeroExt _ n a => emit s "zero_extend" [← writeExprWith keyOf a] [("amount", toJson n)]
  | _, .signExt _ n a => emit s "sign_extend" [← writeExprWith keyOf a] [("amount", toJson n)]
  | _, .extract spec a => emit s "extract" [← writeExprWith keyOf a] [("hi", toJson spec.hi), ("lo", toJson spec.lo)]
  if let some address := address then
    modify fun state => { state with
      visited := state.visited.insert address index
      retained := ⟨Γ, .mk s e⟩ :: state.retained }
  return index
private partial def writeBindingsWith {Γ Δ : Ctx} (keyOf : NodeKey) (bs : Bindings Γ Δ) : StateM Writer (List Json × List Nat) := do
  match Δ, bs with
  | _, .nil => return ([], [])
  | _, .cons name sort rhs rest =>
    let index ← writeExprWith keyOf rhs
    let (decls, indices) ← writeBindingsWith keyOf rest
    return (Json.mkObj [("name", toJson name), ("sort", sortJson sort)] :: decls, index :: indices)
end

private def writeRootsDagWith {Γ : Ctx} (keyOf : NodeKey) (roots : List (TypedExpr Γ)) : Json := Id.run do
  let action := roots.mapM fun (.mk _ e) => writeExprWith keyOf e
  let (indices, state) := action.run {}
  return Json.mkObj [("encoding", toJson "typed-expr-roots-dag-v1"),
    ("roots", toJson indices), ("nodes", toJson state.nodes)]

/-- Runtime identity memoization: check before descending, retain referenced nodes.
Context erasure is safe for serialization: indices, not names resolved through
contexts, identify variables; the cache key also includes the serialized sort because runtime erasure can
share a polymorphic variable object across distinct sorts. -/
private unsafe def writeRootsDagCached {Γ : Ctx} (roots : List (TypedExpr Γ)) : Json :=
  writeRootsDagWith (fun e => some (ptrAddrUnsafe e)) roots

/-- Canonical shared DAG output. The logical definition is the structural
writer; compiled execution adds input-identity memoization to the same traversal.
This runtime optimization is tested, not asserted as a proved codec theorem. -/
@[implemented_by writeRootsDagCached]
def writeRootsDag {Γ : Ctx} (roots : List (TypedExpr Γ)) : Json :=
  writeRootsDagWith (fun _ => none) roots

end Ayxg.QfAbv.JsonCodec
