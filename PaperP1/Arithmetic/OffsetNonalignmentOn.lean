module

public import PaperP1.Arithmetic.ActualOffsetNonalignment

/-! # Exact nonalignment restricted to retained physical positions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetNonalignmentOn

open PaperP1.NormalizedUnitCount

variable {ι : Type*}

def NoExactOn (X : ι → ℕ) (L : ℕ) (P : ι × Fin (L + 1) → Prop) : Prop :=
  ∀ i j : ι, i ≠ j → ∀ u₁ u₂ v₁ v₂ : Fin (L + 1),
    P (i, u₁) → P (i, u₂) → P (j, v₁) → P (j, v₂) →
    (offset u₁, offset v₁) ≠ (offset u₂, offset v₂) →
      ((X i : ℤ) + offset u₁) * ((X j : ℤ) + offset v₂) ≠
        ((X i : ℤ) + offset u₂) * ((X j : ℤ) + offset v₁)

theorem of_global (X : ι → ℕ) (L : ℕ) (P : ι × Fin (L + 1) → Prop)
    (h : ∀ i j, i ≠ j → ActualOffsetNonalignment.NoExact (X i) (X j) L) : NoExactOn X L P := by
  intro i j hij u₁ u₂ v₁ v₂ _hu₁ _hu₂ _hv₁ _hv₂ hne
  exact h i j hij u₁ u₂ v₁ v₂ hne

theorem mono (X : ι → ℕ) (L : ℕ) (P Q : ι × Fin (L + 1) → Prop)
    (h : NoExactOn X L P) (hQP : ∀ v, Q v → P v) : NoExactOn X L Q := by
  intro i j hij u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
  exact h i j hij u₁ u₂ v₁ v₂ (hQP _ hu₁) (hQP _ hu₂) (hQP _ hv₁) (hQP _ hv₂) hne

end PaperP1.OffsetNonalignmentOn
