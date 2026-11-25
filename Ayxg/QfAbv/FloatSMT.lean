import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
AYXG's SMT-LIB rounding-mode adapter over FloatLib's public IEEE runtime API.
SMT's `RNA` maps to FloatLib's IEEE `nearestAway`; the other four modes map
directly. The upstream runtime operations are not a drop-in replacement for
the former `SMT.Proof` API, so this adapter keeps AYXG's solver-facing surface
local and explicit.
-/
namespace FloatLib.Floats.Formats.BinaryInterchange.Model.SMT

inductive RoundingMode where
  | rne | rna | rtp | rtn | rtz
  deriving DecidableEq, Repr

def RoundingMode.ieee : RoundingMode → IEEERoundingMode
  | .rne => .nearest
  | .rna => .nearestAway
  | .rtp => .up
  | .rtn => .down
  | .rtz => .towardZero

def add {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  Model.add x y mode.ieee

def sub {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  Model.sub x y mode.ieee

def mul {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  Model.mul x y mode.ieee

def div {fmt : FloatFormat} (mode : RoundingMode) (x y : Model fmt) : Model fmt :=
  Model.div x y mode.ieee

def fma {fmt : FloatFormat} (mode : RoundingMode) (x y z : Model fmt) : Model fmt :=
  Model.fma x y z mode.ieee

def sqrt {fmt : FloatFormat} (mode : RoundingMode) (x : Model fmt) : Model fmt :=
  Model.sqrt x mode.ieee

def roundToIntegral {fmt : FloatFormat} (mode : RoundingMode) (x : Model fmt) : Model fmt :=
  Model.roundToIntegral x mode.ieee

def roundToInt (mode : RoundingMode) (value : Numerics.Dyadic) : Int :=
  Model.roundDyadicToInt mode.ieee value

def roundDyadic (fmt : FloatFormat) (mode : RoundingMode) (value : Numerics.Dyadic) : Model fmt :=
  Model.Internal.Directed.roundDyadic fmt mode.ieee value

def cast (src dst : FloatFormat) (mode : RoundingMode) (x : Model src) : Model dst :=
  Model.cast src dst x mode.ieee

end FloatLib.Floats.Formats.BinaryInterchange.Model.SMT
