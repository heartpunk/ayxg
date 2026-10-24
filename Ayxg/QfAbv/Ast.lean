import Ayxg.QfAbv.FpTypes

/-
A compact intrinsically typed QF_ABV expression AST used for the concrete
executor spine.

The core expression language is indexed by an SMT-LIB-style declaration context.
Variable occurrences are typed context-membership witnesses rather than runtime
string lookups. This keeps evaluation total while preserving named declarations
and parallel `let` in the semantic core.
-/

namespace Ayxg
namespace QfAbv

/-- QF_ABV term sorts used by the core expression language. -/
inductive TermSort where
  | bool : TermSort
  | bv : Nat → TermSort
  | array : Nat → Nat → TermSort
  | fp : FPFormat → TermSort
  | roundingMode : TermSort
  deriving DecidableEq, Repr

/-- Fixed bit-vector binary operators currently implemented by the compact AST.

This is an initial QF_BV subset, not full SMT-LIB QF_ABV coverage. Missing
operators still include signed remainder, rotates, repeat, `bvcomp`, and
several derived bitwise variants such as nand/nor/xnor.
-/
inductive BvBinOp where
  | add | sub | mul | udiv | sdiv | urem | and | or | xor | shl | lshr | ashr
  deriving DecidableEq, Repr

/-- A named sorted declaration. Names are retained for parsing/printing/provenance;
    evaluation uses positions, not string lookup. -/
structure Decl where
  name : String
  sort : TermSort
  deriving DecidableEq, Repr

/-- Typing context. Convention: the head is the most recent/innermost binding. -/
abbrev Ctx := List Decl

/-- A typed de Bruijn variable: proof that context `Γ` contains a value of sort `s`. -/
inductive Var : Ctx → TermSort → Type where
  | here : Var (d :: Γ) d.sort
  | there : Var Γ s → Var (d :: Γ) s

/-- Well-formed extraction bounds for extracting from a bit-vector of width `w`. -/
structure ExtractSpec (w : Nat) where
  hi : Nat
  lo : Nat
  hi_lt_width : hi < w
  lo_le_hi : lo ≤ hi

/-- The resulting width of an extraction. -/
def ExtractSpec.width {w : Nat} (spec : ExtractSpec w) : Nat :=
  spec.hi - spec.lo + 1

mutual

/-- Typed QF_ABV expressions over a declaration context. -/
inductive Expr : Ctx → TermSort → Type where
  | var : Var Γ s → Expr Γ s
  | boolLit : Bool → Expr Γ .bool
  /-- Bit-vector literal. Evaluation uses `BitVec.ofNat w v` (modulo width);
      SMT-LIB elaboration should range-check/canonicalize literals explicitly. -/
  | bvLit : (w : Nat) → (v : Nat) → Expr Γ (.bv w)
  /-- SMT-style constant array. The element expression is evaluated once, and
      every index maps to that value. -/
  | rmLit : RoundingMode → Expr Γ .roundingMode
  | fpFromBits : (f : FPFormat) → Expr Γ (.bv f.bitWidth) → Expr Γ (.fp f)
  | fpToBits : (f : FPFormat) → Expr Γ (.fp f) → Expr Γ (.bv f.bitWidth)
  | fpUnary : FpUnaryOp → (f : FPFormat) → Expr Γ (.fp f) → Expr Γ (.fp f)
  | fpBinary : FpBinaryOp → (f : FPFormat) → Expr Γ (.fp f) → Expr Γ (.fp f) → Expr Γ (.fp f)
  | fpRounded : FpRoundedOp → (f : FPFormat) → Expr Γ .roundingMode → Expr Γ (.fp f) → Expr Γ (.fp f) → Expr Γ (.fp f)
  | fpFma : (f : FPFormat) → Expr Γ .roundingMode → Expr Γ (.fp f) → Expr Γ (.fp f) → Expr Γ (.fp f) → Expr Γ (.fp f)
  | fpSqrt : (f : FPFormat) → Expr Γ .roundingMode → Expr Γ (.fp f) → Expr Γ (.fp f)
  | fpRoundToIntegral : (f : FPFormat) → Expr Γ .roundingMode → Expr Γ (.fp f) → Expr Γ (.fp f)
  | fpCompare : FpCompareOp → (f : FPFormat) → Expr Γ (.fp f) → Expr Γ (.fp f) → Expr Γ .bool
  | fpClassify : FpClassifyOp → (f : FPFormat) → Expr Γ (.fp f) → Expr Γ .bool
  | fpToBv : (signed : Bool) → (f : FPFormat) → (width : Nat) → Expr Γ .roundingMode → Expr Γ (.fp f) → Expr Γ (.bv width)
  | fpFromBv : (signed : Bool) → (width : Nat) → (f : FPFormat) → Expr Γ .roundingMode → Expr Γ (.bv width) → Expr Γ (.fp f)
  | fpCast : (src dst : FPFormat) → Expr Γ .roundingMode → Expr Γ (.fp src) → Expr Γ (.fp dst)
  | eqFp : (f : FPFormat) → Expr Γ (.fp f) → Expr Γ (.fp f) → Expr Γ .bool
  | eqRoundingMode : Expr Γ .roundingMode → Expr Γ .roundingMode → Expr Γ .bool
  | constArray : (iw vw : Nat) → Expr Γ (.bv vw) → Expr Γ (.array iw vw)
  | boolNot : Expr Γ .bool → Expr Γ .bool
  | boolAnd : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | boolOr : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | ite : Expr Γ .bool → Expr Γ s → Expr Γ s → Expr Γ s
  | bvBin : BvBinOp → (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w) → Expr Γ (.bv w)
  | bvNot : (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w)
  | zeroExt : (w : Nat) → (n : Nat) → Expr Γ (.bv w) → Expr Γ (.bv (w + n))
  | signExt : (w : Nat) → (n : Nat) → Expr Γ (.bv w) → Expr Γ (.bv (w + n))
  | extract : (spec : ExtractSpec w) → Expr Γ (.bv w) → Expr Γ (.bv spec.width)
  | concat : (wHi wLo : Nat) → Expr Γ (.bv wHi) → Expr Γ (.bv wLo) → Expr Γ (.bv (wHi + wLo))
  | select : (iw vw : Nat) → Expr Γ (.array iw vw) → Expr Γ (.bv iw) → Expr Γ (.bv vw)
  | store : (iw vw : Nat) → Expr Γ (.array iw vw) → Expr Γ (.bv iw) → Expr Γ (.bv vw) → Expr Γ (.array iw vw)
  | bvUlt : (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w) → Expr Γ .bool
  | bvUle : (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w) → Expr Γ .bool
  | bvSlt : (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w) → Expr Γ .bool
  | bvSle : (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w) → Expr Γ .bool
  | eqBool : Expr Γ .bool → Expr Γ .bool → Expr Γ .bool
  | eqBv : (w : Nat) → Expr Γ (.bv w) → Expr Γ (.bv w) → Expr Γ .bool
  | eqArray : (iw vw : Nat) → Expr Γ (.array iw vw) → Expr Γ (.array iw vw) → Expr Γ .bool
  /-- Parallel SMT-LIB-style let: all RHSs in `bs` are typed in the old context `Γ`;
      the body is typed in the extended context `Γ'`. -/
  | letPar : Bindings Γ Γ' → Expr Γ' s → Expr Γ s

/-- A parallel binding group from old context `Γ` to extended context `Γ'`.
    Every RHS is typed in old `Γ`, so sibling binders are not visible to RHSs. -/
inductive Bindings : Ctx → Ctx → Type where
  | nil : Bindings Γ Γ
  | cons : (name : String) → (sort : TermSort) →
      Expr Γ sort → Bindings Γ Γ' →
      Bindings Γ ({ name := name, sort := sort } :: Γ')

end

/-- Existential wrapper for expressions whose sort is not statically known to callers. -/
inductive TypedExpr (Γ : Ctx) where
  | mk (s : TermSort) (expr : Expr Γ s) : TypedExpr Γ

namespace TypedExpr

def sort {Γ : Ctx} : TypedExpr Γ → TermSort
  | .mk s _ => s

end TypedExpr

end QfAbv
end Ayxg
