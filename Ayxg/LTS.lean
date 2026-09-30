/-
Minimal labeled transition systems.

This is deliberately CSLib-shaped without importing CSLib yet: a state type,
a label type, and a relational transition semantics. Distinguished initial
states belong in pointed wrappers or examples, not in the LTS core.
-/

namespace Ayxg

/-- A labeled transition system over states `S` and labels `L`. -/
structure LTS (S L : Type) where
  Tr : S → L → S → Prop

namespace LTS

variable {S L : Type}

/-- Label-erased one-step reachability. -/
def canStep (lts : LTS S L) (s s' : S) : Prop :=
  ∃ l, lts.Tr s l s'

/-- Reachability from an explicit starting state, avoiding an external
transitive-closure dependency while keeping the LTS itself unpointed. -/
inductive ReachableFrom (lts : LTS S L) (start : S) : S → Prop where
  | refl : ReachableFrom lts start start
  | step {s s' : S} {l : L} :
      ReachableFrom lts start s → lts.Tr s l s' → ReachableFrom lts start s'

/-- A labeled trace between two states. -/
inductive IsTrace (lts : LTS S L) : S → List L → S → Prop where
  | nil (s : S) : IsTrace lts s [] s
  | cons (l : L) {s₁ s₂ s₃ : S} (ls : List L) :
      lts.Tr s₁ l s₂ → IsTrace lts s₂ ls s₃ → IsTrace lts s₁ (l :: ls) s₃

/-- A singleton trace is exactly one labeled transition. -/
theorem IsTrace.singleton_iff {lts : LTS S L} {s s' : S} {l : L} :
    IsTrace lts s [l] s' ↔ lts.Tr s l s' := by
  constructor
  · intro h
    cases h with
    | cons _ _ hstep htail =>
        cases htail
        exact hstep
  · intro h
    exact .cons l [] h (.nil s')

/-- Label-erased one-step reachability is the existence of a singleton trace. -/
theorem canStep_iff_singleton_trace {lts : LTS S L} {s s' : S} :
    lts.canStep s s' ↔ ∃ l, IsTrace lts s [l] s' := by
  constructor
  · rintro ⟨l, hstep⟩
    exact ⟨l, (IsTrace.singleton_iff).2 hstep⟩
  · rintro ⟨l, htrace⟩
    exact ⟨l, (IsTrace.singleton_iff).1 htrace⟩

theorem IsTrace.append {lts : LTS S L} {s₁ s₂ s₃ : S} {ls₁ ls₂ : List L}
    (h₁ : IsTrace lts s₁ ls₁ s₂) (h₂ : IsTrace lts s₂ ls₂ s₃) :
    IsTrace lts s₁ (ls₁ ++ ls₂) s₃ := by
  induction h₁ with
  | nil => exact h₂
  | cons l ls hstep _ ih => exact .cons l (ls ++ ls₂) hstep (ih h₂)

/-- A trace from any reachable state reaches its endpoint. -/
theorem IsTrace.toReachableFrom {lts : LTS S L} {start s₁ s₂ : S} {ls : List L}
    (hr : ReachableFrom lts start s₁) (h : IsTrace lts s₁ ls s₂) :
    ReachableFrom lts start s₂ := by
  induction h with
  | nil => exact hr
  | cons _ _ hstep _ ih => exact ih (.step hr hstep)

end LTS
end Ayxg
