module

public import PaperP1.Arithmetic.OffsetNonalignmentOn

/-! # Nonalignment from one distinguished block to the remaining blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetNonalignmentFrom

open PaperP1.NormalizedUnitCount

variable {ι : Type*}

def NoExactFrom (X : ι → ℕ) (L : ℕ) (P : ι × Fin (L + 1) → Prop) (i : ι) : Prop :=
  ∀ j : ι, j ≠ i → ∀ u₁ u₂ v₁ v₂ : Fin (L + 1),
    P (i, u₁) → P (i, u₂) → P (j, v₁) → P (j, v₂) →
    (offset u₁, offset v₁) ≠ (offset u₂, offset v₂) →
      ((X i : ℤ) + offset u₁) * ((X j : ℤ) + offset v₂) ≠
        ((X i : ℤ) + offset u₂) * ((X j : ℤ) + offset v₁)

theorem of_global (X : ι → ℕ) (L : ℕ) (P : ι × Fin (L + 1) → Prop) (i : ι)
    (h : ∀ j, j ≠ i → ActualOffsetNonalignment.NoExact (X i) (X j) L) : NoExactFrom X L P i := by
  intro j hji u₁ u₂ v₁ v₂ _hu₁ _hu₂ _hv₁ _hv₂ hne
  exact h j hji u₁ u₂ v₁ v₂ hne

theorem of_all (X : ι → ℕ) (L : ℕ) (P : ι × Fin (L + 1) → Prop) (i : ι)
    (h : OffsetNonalignmentOn.NoExactOn X L P) : NoExactFrom X L P i := by
  intro j hji
  exact h i j hji.symm

theorem mono (X : ι → ℕ) (L : ℕ) (P Q : ι × Fin (L + 1) → Prop) (i : ι)
    (h : NoExactFrom X L P i) (hQP : ∀ v, Q v → P v) : NoExactFrom X L Q i := by
  intro j hji u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
  exact h j hji u₁ u₂ v₁ v₂ (hQP _ hu₁) (hQP _ hu₂) (hQP _ hv₁) (hQP _ hv₂) hne

end PaperP1.OffsetNonalignmentFrom
