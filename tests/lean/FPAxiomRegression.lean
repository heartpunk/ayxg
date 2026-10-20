import Ayxg.LTS.QfAbv.SymbolicStep

open Ayxg.QfAbv
open FloatLib.Floats.Formats.BinaryInterchange

-- The format and field-extraction values are definitionally unchanged.
example (f : FPFormat) :
    f.floatFormat = FloatFormat.ieee f.exponentBits (f.significandBits - 1)
      f.exponent_ge_two (by have := f.significand_ge_two; omega) := rfl

example {fmt : FloatFormat} (x : Model fmt) :
    x.expField = ((x.bits >>> fmt.fracWidth) &&& FloatFormat.expAllOnes fmt).toNat := rfl

example {fmt : FloatFormat} (x : Model fmt) :
    x.fracField = (x.bits &&& FloatFormat.fracMask fmt).toNat := rfl

/-- info: 'Ayxg.QfAbv.Env' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ayxg.QfAbv.Env

/-- info: 'Ayxg.LTS.QfAbv.SymbolicTransitionSystem.symbolicStep_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ayxg.LTS.QfAbv.SymbolicTransitionSystem.symbolicStep_length
