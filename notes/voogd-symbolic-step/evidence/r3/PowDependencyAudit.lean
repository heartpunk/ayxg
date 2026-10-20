import Ayxg.LTS.QfAbv.SymbolicStep

#print axioms Nat.pow_lt_pow_of_lt
#print axioms Nat.pow_lt_pow_iff_right
#print Nat.pow_lt_pow_iff_right

open FloatLib.Floats.Formats.BinaryInterchange

-- Same bound used by FloatFormat.ieee, with the direct implication theorem.
theorem ieeeBias_bound_without_choice (expWidth : Nat) (h : 2 ≤ expWidth) :
    FloatFormat.ieeeBias expWidth ≤
      FloatFormat.Encoding.maxFiniteExponent .ieee expWidth := by
  have hwidthPos : 0 < expWidth := by omega
  have hindex : expWidth - 1 < expWidth := Nat.sub_lt hwidthPos (by decide)
  have hpow : 2 ^ (expWidth - 1) < 2 ^ expWidth :=
    Nat.pow_lt_pow_of_lt (by decide) hindex
  change 2 ^ (expWidth - 1) - 1 ≤ 2 ^ expWidth - 2
  omega

#print axioms ieeeBias_bound_without_choice
