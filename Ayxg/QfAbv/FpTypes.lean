namespace Ayxg.QfAbv
/-- SMT-LIB floating-point format: significand width includes the hidden bit. -/
structure FPFormat where
  exponentBits : Nat
  significandBits : Nat
  exponent_ge_two : 2 ≤ exponentBits
  significand_ge_two : 2 ≤ significandBits
  deriving DecidableEq, Repr

def FPFormat.bitWidth (f : FPFormat) : Nat := f.exponentBits + f.significandBits

inductive RoundingMode where
  | rne | rna | rtp | rtn | rtz
  deriving DecidableEq, Repr
inductive FpUnaryOp where
  | abs | neg
  deriving DecidableEq, Repr
inductive FpBinaryOp where
  | rem | min | max
  deriving DecidableEq, Repr
inductive FpRoundedOp where
  | add | sub | mul | div
  deriving DecidableEq, Repr
inductive FpCompareOp where
  | eq | lt | le | gt | ge
  deriving DecidableEq, Repr
inductive FpClassifyOp where
  | normal | subnormal | zero | infinite | nan | negative | positive
  deriving DecidableEq, Repr
end Ayxg.QfAbv
