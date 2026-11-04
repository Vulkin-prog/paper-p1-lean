module

public import PaperP1.Analysis.ReducedSourceParameter

/-! # Source monomial comparisons for the normalized reduced box and integer parameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedSourceMonomials

open PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter

theorem quotient_identity (c D U : ℝ) (g q : ℕ) (hg : 0 < g) (hq : 0 < q) :
    c * (D / g) ^ 2 * (U / q) = (c * D ^ 2 * U) / ((g ^ 2 * q : ℕ) : ℝ) := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp [hgR, hqR]

theorem source_bounds (N g q : ℕ) (ρ C c D U : ℝ) (hg : 0 < g) (hq : 0 < q)
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hc : 0 ≤ c) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hhalfD : 1 / 2 ≤ D / g) (hhalfU : 1 / 2 ≤ U / q)
    (hlower : ρ * N ≤ c * D ^ 2 * U) (hupper : c * D ^ 2 * U ≤ C * N)
    (heffective : 1 ≤ effective N (g ^ 2 * q)) :
    (ρ / 2) * (parameter N (g ^ 2 * q) : ℝ) ≤ c * enlarged D g ^ 2 * enlarged U q ∧
      c * enlarged D g ^ 2 * enlarged U q ≤ (8 * C) * parameter N (g ^ 2 * q) := by
  have hsR : (0 : ℝ) < ((g ^ 2 * q : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos hg 2) hq
  have hrawLow : ρ * effective N (g ^ 2 * q) ≤ c * (D / g) ^ 2 * (U / q) := by
    unfold effective
    rw [quotient_identity c D U g q hg hq]
    have ht := div_le_div_of_nonneg_right hlower hsR.le
    convert ht using 1
    ring
  have hrawUp : c * (D / g) ^ 2 * (U / q) ≤ C * effective N (g ^ 2 * q) := by
    unfold effective
    rw [quotient_identity c D U g q hg hq]
    have ht := div_le_div_of_nonneg_right hupper hsR.le
    convert ht using 1
    ring
  have hpUpper := parameter_upper N (g ^ 2 * q) heffective
  have hpLower := effective_le_parameter N (g ^ 2 * q)
  constructor
  · have ht := mul_le_mul_of_nonneg_left hpUpper (by positivity : 0 ≤ ρ / 2)
    calc
      _ ≤ ρ * effective N (g ^ 2 * q) := by nlinarith only [ht]
      _ ≤ c * (D / g) ^ 2 * (U / q) := hrawLow
      _ ≤ _ := source_product_lower c D U g q hc hD hU
  · calc
      _ ≤ 8 * (c * (D / g) ^ 2 * (U / q)) := source_product_upper c D U g q hc hhalfD hhalfU
      _ ≤ 8 * (C * effective N (g ^ 2 * q)) := mul_le_mul_of_nonneg_left hrawUp (by norm_num)
      _ = (8 * C) * effective N (g ^ 2 * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpLower (by positivity : 0 ≤ 8 * C)

end PaperP1.ReducedSourceMonomials
