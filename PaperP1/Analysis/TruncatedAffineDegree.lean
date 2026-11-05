module

public import PaperP1.Arithmetic.DegreeUniformAffineParameters

/-! # Truncating the auxiliary vertical degree at the logarithmic budget

The auxiliary polynomial need only have vertical degree below the curve's
vertical degree. At larger curve degrees a logarithmic truncation suffices.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TruncatedAffineDegree

open DegreeUniformAffineParameters

def effectiveDegree (D N : ℕ) : ℕ := min D (logarithmicBudget N + 1)

theorem budget (D N : ℕ) (hD : 2 ≤ D) :
    2 ≤ effectiveDegree D N ∧ effectiveDegree D N ≤ D ∧
      effectiveDegree D N - 1 < D ∧
      auxiliaryDegree N + (effectiveDegree D N - 1) ≤ 5 * logarithmicBudget N := by
  have hL : 1 ≤ logarithmicBudget N := by unfold logarithmicBudget; omega
  have hb : 2 ≤ effectiveDegree D N := le_min hD (by omega)
  have hbD : effectiveDegree D N ≤ D := min_le_left _ _
  have hbL : effectiveDegree D N ≤ logarithmicBudget N + 1 := min_le_right _ _
  refine ⟨hb, hbD, by omega, ?_⟩
  unfold auxiliaryDegree
  omega

theorem prime_scale (D N : ℕ) (H P : ℝ) (hH : 1 ≤ H)
    (hlog : Real.log H ≤ 3 * logarithmicBudget N)
    (hold : 3 * Real.exp 1 * H ^ (1 / (D : ℝ)) ≤ P)
    (hconstant : 3 * Real.exp 4 ≤ P) :
    3 * Real.exp 1 * H ^ (1 / (effectiveDegree D N : ℝ)) ≤ P := by
  by_cases hD : D ≤ logarithmicBudget N + 1
  · simpa only [effectiveDegree, min_eq_left hD] using hold
  · have hmin : effectiveDegree D N = logarithmicBudget N + 1 := min_eq_right (by omega)
    rw [hmin]
    have hHp : 0 < H := by linarith only [hH]
    have hden : (0 : ℝ) < ((logarithmicBudget N + 1 : ℕ) : ℝ) := by positivity
    have hroot : H ^ (1 / ((logarithmicBudget N + 1 : ℕ) : ℝ)) ≤ Real.exp 3 := by
      rw [Real.rpow_def_of_pos hHp]
      apply Real.exp_le_exp.mpr
      have hh : Real.log H / ((logarithmicBudget N + 1 : ℕ) : ℝ) ≤ 3 := by
        apply (div_le_iff₀ hden).mpr
        push_cast
        linarith only [hlog]
      simpa only [mul_one_div] using hh
    calc
      _ ≤ 3 * Real.exp 1 * Real.exp 3 := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 3 * Real.exp 4 := by rw [mul_assoc, ← Real.exp_add]; norm_num
      _ ≤ _ := hconstant

end PaperP1.TruncatedAffineDegree
