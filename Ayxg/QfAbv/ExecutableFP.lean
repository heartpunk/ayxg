import Ayxg.QfAbv.FpEval

namespace Ayxg.QfAbv

/-- One explicit executable choice for the SMT operations whose results are
underspecified. NaN bit extraction uses the canonical value's raw encoding;
invalid float-to-bitvector conversion returns zero; opposite-zero min/max ties
keep the left sign. This is named rather than installed as a global instance. -/
@[instance_reducible] def FPInterpretation.executableChoice : FPInterpretation where
  nanBits := fun _ x _ => x.rawBits
  nanBits_isNaN := by
    intro f x h
    rw [FPValue.rawBits_roundtrip]
    exact h
  invalidToBV := fun _ _ _ _ _ => 0
  zeroTie := fun _ _ leftNegative => leftNegative

end Ayxg.QfAbv
