import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finite
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
AYXG's SMT-LIB five-mode adapter over FloatLib's public IEEE runtime API.
SMT's `RNA` is FloatLib's deterministic `nearestAway`; the other four modes
map directly to their IEEE rounding directions. Keep this boundary local to
AYXG: the upstream Model operations are not the former SMT.Proof API.
-/
namespace FloatLib.Floats.Formats.BinaryInterchange.Model.SMT

inductive RoundingMode where
  | rne | rna | rtp | rtn | rtz
  deriving DecidableEq, Repr

def RoundingMode.ieee : RoundingMode → IEEERoundingMode
  | .rne | .rna => .nearestEven
  | .rtp => .towardPositiveInfinity
  | .rtn => .towardNegativeInfinity
  | .rtz => .towardZero

private def rnaPolicy : FloatLib.Numerics.QuantizationPolicy :=
  { rounding := FloatLib.Numerics.RoundingMode.nearestAway }

private def roundDyadicRNA (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  Model.Policy.roundDyadic fmt rnaPolicy 0 value

/-- RNA is an explicit policy in FloatLib, not an IEEE rounding constructor. -/
def RoundingMode.ieee? (mode : RoundingMode) : Option IEEERoundingMode :=
  if mode == .rna then none else some mode.ieee

def add {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  if mode == .rna then
    (Model.addFinite? fmt rnaPolicy 0 x y).getD (Model.addWithRounding .nearestEven x y)
  else Model.addWithRounding mode.ieee x y

def sub {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  if mode == .rna then
    (Model.subFinite? fmt rnaPolicy 0 x y).getD (Model.subWithRounding .nearestEven x y)
  else Model.subWithRounding mode.ieee x y

def mul {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  if mode == .rna then
    (Model.mulFinite? fmt rnaPolicy 0 x y).getD (Model.mulWithRounding .nearestEven x y)
  else Model.mulWithRounding mode.ieee x y

def div {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  if mode == .rna then
    (Model.divFinite? fmt rnaPolicy 0 x y).getD (Model.divWithRounding .nearestEven x y)
  else Model.divWithRounding mode.ieee x y

def fma {fmt : FloatFormat} (mode : RoundingMode) (x y z : Model fmt) : Model fmt :=
  if mode == .rna then
    (Model.fmaFinite? fmt rnaPolicy 0 x y z).getD (Model.fmaWithRounding .nearestEven x y z)
  else Model.fmaWithRounding mode.ieee x y z

private def sqrtRNA {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match Model.toDyadic? x with
  | none => Model.sqrtWithRounding .nearestEven x
  | some exact =>
      if exact.negative || exact.significand == 0 then
        Model.sqrtWithRounding .nearestEven x
      else
        let bracket := Model.sqrtDyadicBracket fmt exact
        let lo := Model.roundDyadicDown fmt bracket.lower
        let hi := Model.roundDyadicUp fmt bracket.upper
        match Model.toDyadic? lo, Model.toDyadic? hi with
        | some loExact, some hiExact =>
            let sum := Model.addDyadic loExact hiExact
            let midpoint : Numerics.Dyadic := { sum with exponent := sum.exponent - 1 }
            if Numerics.Dyadic.isEqual (Model.mulDyadic midpoint midpoint) exact then hi
            else Model.sqrtWithRounding .nearestEven x
        | _, _ => Model.sqrtWithRounding .nearestEven x

def sqrt {fmt : FloatFormat} (_hIEEE : fmt.encoding = .ieee)
    (mode : RoundingMode) (x : Model fmt) : Model fmt :=
  if mode == .rna then sqrtRNA x else Model.sqrtWithRounding mode.ieee x

def roundToIntegral {fmt : FloatFormat} (mode : RoundingMode) (x : Model fmt) : Model fmt :=
  if mode == .rna then
    match Model.toDyadic? x with
    | none => Model.roundToIntegral x .nearestEven
    | some exact =>
        let rounded := roundToInt .rna exact
        roundDyadicRNA fmt { negative := rounded < 0, significand := rounded.natAbs, exponent := 0 }
  else Model.roundToIntegral x mode.ieee

def roundToInt (mode : RoundingMode) (value : Numerics.Dyadic) : Int :=
  if mode == .rna then
    let magnitude := match value.exponent with
      | .ofNat shift => Nat.shiftLeft value.significand shift
      | .negSucc shift =>
          Model.Policy.roundQuot .nearestAway value.negative 0 value.significand
            (Nat.shiftLeft 1 (shift + 1))
    if value.negative then -(Int.ofNat magnitude) else Int.ofNat magnitude
  else Model.roundDyadicToInt mode.ieee value

def roundDyadic (fmt : FloatFormat) (mode : RoundingMode) (value : Numerics.Dyadic) : Model fmt :=
  if mode == .rna then roundDyadicRNA fmt value
  else Model.roundDyadicWithRounding fmt mode.ieee value

def cast (src dst : FloatFormat) (mode : RoundingMode) (x : Model src) : Model dst :=
  if mode == .rna then
    (Model.Policy.castFinite? src dst rnaPolicy 0 x).getD (Model.castWithRounding src dst x .nearestEven)
  else Model.castWithRounding src dst x mode.ieee

end FloatLib.Floats.Formats.BinaryInterchange.Model.SMT
