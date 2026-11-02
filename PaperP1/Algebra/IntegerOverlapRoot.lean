module

public import PaperP1.Algebra.SquareInFractionField
public import PaperP1.Algebra.BiquadraticSourceNorm

/-! # The third root at an integer square point is an actual integer with the required sign -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.IntegerOverlapRoot

theorem exists_root (g f₁ f₂ f₃ w₁ w₂ : ℤ) (hg : g ≠ 0)
    (hrel : f₃ * g ^ 2 = f₁ * f₂) (h₁ : w₁ ^ 2 = f₁) (h₂ : w₂ ^ 2 = f₂) :
    ∃ w₃ : ℤ, w₃ ^ 2 = f₃ ∧ g * w₃ = w₁ * w₂ := by
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hqrel : (f₃ : ℚ) * (g : ℚ) ^ 2 = (w₁ : ℚ) ^ 2 * (w₂ : ℚ) ^ 2 := by
    exact_mod_cast (hrel.trans (by rw [h₁, h₂]))
  have hsq : IsSquare (f₃ : ℚ) := by
    rw [isSquare_iff_exists_sq]
    refine ⟨((w₁ : ℚ) * (w₂ : ℚ)) / (g : ℚ), ?_⟩
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hgq)).mpr
    rw [mul_pow]
    exact hqrel
  have hzi : IsSquare f₃ :=
    (SquareInFractionField.square_reflect (R := ℤ) (K := ℚ) f₃).mp hsq
  obtain ⟨w, hw⟩ := hzi.exists_sq
  have heq : (g * w) ^ 2 = (w₁ * w₂) ^ 2 := by
    rw [mul_pow, ← hw, mul_comm (g ^ 2) f₃, hrel, ← h₁, ← h₂, mul_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with hp | hm
  · exact ⟨w, hw.symm, hp⟩
  · refine ⟨-w, ?_, ?_⟩
    · simpa only [neg_sq] using hw.symm
    · simp only [mul_neg, hm, neg_neg]

end PaperP1.IntegerOverlapRoot
