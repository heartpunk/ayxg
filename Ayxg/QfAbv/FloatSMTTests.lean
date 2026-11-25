import Ayxg.QfAbv.FloatSMT

open FloatLib.Floats.Formats.BinaryInterchange

namespace Ayxg.QfAbv.FloatSMTTests

private def half : FloatLib.Numerics.Dyadic := { negative := false, significand := 1, exponent := -1 }
private def negHalf : FloatLib.Numerics.Dyadic := { negative := true, significand := 1, exponent := -1 }

example : Model.SMT.roundToInt .rne half = 0 := by decide
example : Model.SMT.roundToInt .rna half = 1 := by decide
example : Model.SMT.roundToInt .rtp half = 1 := by decide
example : Model.SMT.roundToInt .rtn half = 0 := by decide
example : Model.SMT.roundToInt .rtz half = 0 := by decide

example : Model.SMT.roundToInt .rne negHalf = 0 := by decide
example : Model.SMT.roundToInt .rna negHalf = -1 := by decide
example : Model.SMT.roundToInt .rtp negHalf = 0 := by decide
example : Model.SMT.roundToInt .rtn negHalf = -1 := by decide
example : Model.SMT.roundToInt .rtz negHalf = 0 := by decide

private def fmt : FloatFormat := FloatFormat.ieee 3 3 (by decide) (by decide)
private def posZero : Model fmt := Model.ofNatBits 0
private def negZero : Model fmt := Model.ofNatBits 64
private def qNaN : Model fmt := Model.ofNatBits 57
private def one : Model fmt := Model.ofNatBits 24
private def oneSixteenth : Model fmt := Model.ofNatBits 2

example : (Model.SMT.add .rne one oneSixteenth).toNatBits = 24 := by decide
example : (Model.SMT.add .rna one oneSixteenth).toNatBits = 25 := by decide
example : (Model.SMT.add .rtp one oneSixteenth).toNatBits = 25 := by decide
example : (Model.SMT.add .rtn one oneSixteenth).toNatBits = 24 := by decide
example : (Model.SMT.add .rtz one oneSixteenth).toNatBits = 24 := by decide

example : (Model.SMT.add .rtn negZero posZero).signBit = true := by decide
example : (Model.SMT.add .rne negZero posZero).signBit = false := by decide
example : (Model.SMT.add .rna qNaN posZero).isNaN = true := by decide

private def negQuarter : Model fmt :=
  Model.roundDyadic fmt { negative := true, significand := 1, exponent := -2 }

example : (Model.SMT.roundToIntegral .rna negQuarter).isZero = true := by decide
example : (Model.SMT.roundToIntegral .rna negQuarter).signBit = true := by decide

end Ayxg.QfAbv.FloatSMTTests
