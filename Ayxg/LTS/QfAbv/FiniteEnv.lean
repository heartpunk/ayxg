import Ayxg.QfAbv.Eval
import Mathlib.Data.List.Pi

namespace Ayxg
namespace LTS
namespace QfAbv

open _root_.Ayxg.QfAbv

/-- An executable list with a proof that it covers its type. -/
structure Coverage (α : Type) where
  values : List α
  complete : ∀ x : α, x ∈ values

/-- All fixed-width bit vectors, enumerated by their finite encodings. -/
def bitVecCoverage (w : Nat) : Coverage (BitVec w) where
  values := List.ofFn (fun i : Fin (2 ^ w) => BitVec.ofFin i)
  complete := by
    intro x
    apply List.mem_ofFn.mpr
    exact ⟨x.toFin, rfl⟩

/-- Decoding an already canonical floating-point value's raw encoding gives
back that value. -/
theorem fpValue_ofBits_rawBits {f : FPFormat} (x : FPValue f) :
    FPValue.ofBits f x.rawBits = x := by
  unfold FPValue.ofBits
  rw [FPValue.rawBits_roundtrip]
  cases x with
  | mk model canonical =>
    by_cases hnan : model.isNaN = true
    · have hmodel : model = canonicalNaN f := by
        rcases canonical with hfalse | heq
        · simp [hfalse] at hnan
        · exact heq
      subst model
      simp [FPValue.ofModel, hnan]
    · simp [FPValue.ofModel, hnan]

/-- The canonical FP carrier is covered by all raw bit encodings. -/
def fpValueCoverage (f : FPFormat) : Coverage (FPValue f) where
  values := (bitVecCoverage f.bitWidth).values.map (FPValue.ofBits f)
  complete := by
    intro x
    apply List.mem_map.mpr
    exact ⟨x.rawBits, (bitVecCoverage f.bitWidth).complete x.rawBits,
      fpValue_ofBits_rawBits x⟩

def roundingModeCoverage : Coverage RoundingMode where
  values := [.rne, .rna, .rtp, .rtn, .rtz]
  complete := by intro mode; cases mode <;> simp

/-- All total arrays over finite bit-vector index and value types. -/
def arrayCoverage (iw vw : Nat) : Coverage (Mem iw vw) := by
  let indices := bitVecCoverage iw
  let values := bitVecCoverage vw
  exact
    { values :=
        (List.pi indices.values (fun _ => values.values)).map
          (fun f i => f i (indices.complete i))
      complete := by
        intro array
        apply List.mem_map.mpr
        let assignment : ∀ i, i ∈ indices.values → BitVec vw :=
          fun i _ => array i
        refine ⟨assignment, ?_, ?_⟩
        · rw [List.mem_pi]
          intro i _
          exact values.complete (array i)
        · funext i
          rfl }

/-- An executable complete enumeration for every QF_ABV semantic sort. -/
def denoteCoverage : (sort : TermSort) → Coverage (Denote sort)
  | .bool =>
      { values := [false, true]
        complete := by intro b; cases b <;> simp }
  | .bv w => bitVecCoverage w
  | .array iw vw => arrayCoverage iw vw
  | .fp f => fpValueCoverage f
  | .roundingMode => roundingModeCoverage

/-- An executable complete enumeration of all environments in a context. -/
def envCoverage : (Γ : Ctx) → Coverage (Env Γ)
  | [] =>
      { values := [.nil]
        complete := by intro env; cases env; simp }
  | d :: Γ =>
      let heads := denoteCoverage d.sort
      let tails := envCoverage Γ
      { values := heads.values.flatMap fun value =>
          tails.values.map (Env.cons value)
        complete := by
          intro env
          cases env with
          | cons value tail =>
              apply List.mem_flatMap.mpr
              refine ⟨value, heads.complete value, ?_⟩
              apply List.mem_map.mpr
              exact ⟨tail, tails.complete tail, rfl⟩ }

/-- The list used by the region emptiness checker. -/
def enumerateEnv (Γ : Ctx) : List (Env Γ) := (envCoverage Γ).values

theorem mem_enumerateEnv {Γ : Ctx} (env : Env Γ) :
    env ∈ enumerateEnv Γ := (envCoverage Γ).complete env

end QfAbv
end LTS
end Ayxg
