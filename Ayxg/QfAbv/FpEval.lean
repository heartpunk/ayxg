import Ayxg.QfAbv.FpTypes
import FloatLib.Floats.Formats.BinaryInterchange.SMT.Proof

namespace Ayxg.QfAbv
open FloatLib.Floats.Formats.BinaryInterchange

def FPFormat.floatFormat (f : FPFormat) : FloatFormat :=
  FloatFormat.ieee f.exponentBits (f.significandBits - 1)
    f.exponent_ge_two (Nat.sub_pos_of_lt f.significand_ge_two)

def canonicalNaN (f : FPFormat) : Model f.floatFormat :=
  Model.ofNatBits (((2 ^ f.exponentBits - 1) * 2 ^ (f.significandBits - 1)) + 1)

/-- One SMT NaN value; payload and sign are erased at the carrier boundary. -/
structure FPValue (f : FPFormat) where
  model : Model f.floatFormat
  canonical : model.isNaN = false ∨ model = canonicalNaN f
  deriving DecidableEq, Repr

def FPValue.ofModel {f : FPFormat} (value : Model f.floatFormat) : FPValue f :=
  if h : value.isNaN = true then ⟨canonicalNaN f, Or.inr rfl⟩
  else ⟨value, Or.inl (by cases hv : value.isNaN <;> simp_all)⟩

def FPValue.ofBits (f : FPFormat) (bits : BitVec f.bitWidth) : FPValue f :=
  ofModel (Model.ofNatBits bits.toNat)

theorem FPFormat.floatFormat_bitWidth (f : FPFormat) : f.floatFormat.bitWidth = f.bitWidth := by
  simp only [FPFormat.floatFormat, FloatFormat.bitWidth, FloatFormat.ieee, FPFormat.bitWidth]
  have := f.significand_ge_two
  omega

def FPValue.rawBits {f : FPFormat} (x : FPValue f) : BitVec f.bitWidth :=
  BitVec.ofNat f.bitWidth x.model.toNatBits

theorem FPValue.rawBits_roundtrip {f : FPFormat} (x : FPValue f) :
    Model.ofNatBits (fmt := f.floatFormat) x.rawBits.toNat = x.model := by
  have hlt : x.model.toNatBits < 2 ^ f.bitWidth := by
    simpa [FPFormat.floatFormat_bitWidth] using x.model.toNatBits_lt_two_pow
  simp only [FPValue.rawBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact Model.ofNatBits_toNatBits x.model

/-- A consistent interpretation of the genuinely underspecified applications.
There is deliberately no default instance. The NaN encoding constraint is
specific to the Z3 fp.to_ieee_bv extension, not a standard SMT-LIB operator. -/
class FPInterpretation where
  nanBits : (f : FPFormat) → (x : FPValue f) → x.model.isNaN = true → BitVec f.bitWidth
  nanBits_isNaN : ∀ f x h, (Model.ofNatBits (fmt := f.floatFormat) (nanBits f x h).toNat).isNaN = true
  invalidToBV : (signed : Bool) → (f : FPFormat) → (width : Nat) →
    RoundingMode → FPValue f → BitVec width
  zeroTie : (isMin : Bool) → (f : FPFormat) → (leftNegative : Bool) → Bool

namespace FPEval
variable [FPInterpretation]

def mode : RoundingMode → Model.SMT.RoundingMode
  | .rne => .rne | .rna => .rna | .rtp => .rtp | .rtn => .rtn | .rtz => .rtz

def toBits {f : FPFormat} (x : FPValue f) : BitVec f.bitWidth :=
  if h : x.model.isNaN = true then FPInterpretation.nanBits f x h
  else x.rawBits

def unary {f : FPFormat} (op : FpUnaryOp) (x : FPValue f) : FPValue f :=
  FPValue.ofModel (match op with | .abs => Model.abs x.model | .neg => Model.neg x.model)

def binary {f : FPFormat} (op : FpBinaryOp) (x y : FPValue f) : FPValue f :=
  FPValue.ofModel <| match op with
  | .rem => Model.remainder x.model y.model
  | .min | .max =>
      if x.model.isZero && y.model.isZero && (x.model.signBit != y.model.signBit) then
        Model.zero f.floatFormat (FPInterpretation.zeroTie (op == .min) f x.model.signBit)
      else if op == .min then Model.minimumNumber x.model y.model
      else Model.maximumNumber x.model y.model

def rounded {f : FPFormat} (op : FpRoundedOp) (rm : RoundingMode) (x y : FPValue f) : FPValue f :=
  FPValue.ofModel <| match op with
  | .add => Model.SMT.add (mode rm) x.model y.model
  | .sub => Model.SMT.sub (mode rm) x.model y.model
  | .mul => Model.SMT.mul (mode rm) x.model y.model
  | .div => Model.SMT.div (mode rm) x.model y.model

def fma {f : FPFormat} (rm : RoundingMode) (x y z : FPValue f) : FPValue f :=
  FPValue.ofModel (Model.SMT.fma (mode rm) x.model y.model z.model)
def sqrt {f : FPFormat} (rm : RoundingMode) (x : FPValue f) : FPValue f :=
  FPValue.ofModel (Model.SMT.sqrt (by rfl) (mode rm) x.model)
def roundToIntegral {f : FPFormat} (rm : RoundingMode) (x : FPValue f) : FPValue f :=
  FPValue.ofModel (Model.SMT.roundToIntegral (mode rm) x.model)

def compare {f : FPFormat} (op : FpCompareOp) (x y : FPValue f) : Bool :=
  match Model.compare x.model y.model with
  | none => false
  | some order => match op with
    | .eq => order == .eq | .lt => order == .lt | .le => order != .gt
    | .gt => order == .gt | .ge => order != .lt

def classify {f : FPFormat} (op : FpClassifyOp) (x : FPValue f) : Bool :=
  match op with
  | .normal => x.model.expField != 0 && x.model.isFinite | .subnormal => x.model.isSubnormal
  | .zero => x.model.isZero | .infinite => x.model.isInf | .nan => x.model.isNaN
  | .negative => !x.model.isNaN && x.model.signBit
  | .positive => !x.model.isNaN && !x.model.signBit

def toBV {f : FPFormat} (signed : Bool) (width : Nat) (rm : RoundingMode) (x : FPValue f) : BitVec width :=
  match Model.toDyadic? x.model with
  | none => FPInterpretation.invalidToBV signed f width rm x
  | some dx =>
      let n := Model.SMT.roundToInt (mode rm) dx
      let low : Int := if signed then -(2 ^ (width - 1) : Nat) else 0
      let high : Int := if signed then (2 ^ (width - 1) : Nat) else (2 ^ width : Nat)
      if low ≤ n && n < high then BitVec.ofInt width n
      else FPInterpretation.invalidToBV signed f width rm x

def fromBV (signed : Bool) (f : FPFormat) (rm : RoundingMode) {width : Nat} (x : BitVec width) : FPValue f :=
  let n : Int := if signed then x.toInt else x.toNat
  let exact : FloatLib.Numerics.Dyadic := { negative := n < 0, significand := n.natAbs, exponent := 0 }
  FPValue.ofModel <| match (mode rm).ieee? with
  | some ieee => Model.roundDyadicWithRounding f.floatFormat ieee exact
  | none => Model.SMT.roundRNA f.floatFormat exact

def cast (src dst : FPFormat) (rm : RoundingMode) (x : FPValue src) : FPValue dst :=
  FPValue.ofModel (Model.SMT.cast src.floatFormat dst.floatFormat (mode rm) x.model)
end FPEval
end Ayxg.QfAbv
