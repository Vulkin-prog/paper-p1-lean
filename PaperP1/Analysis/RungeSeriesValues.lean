module

public import PaperP1.Analysis.RealSeriesTail

/-! # The convergent formal Runge factors are the positive real square-root branches -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RungeSeriesValues

open Finset PaperP1.RealSeriesEvaluation PaperP1.RungePowerSeries

theorem factor_coefficient_bound (γ : ℤ) (n : ℕ) :
    |((PowerSeries.coeff n (sqrtFactorSeries γ) : ℚ) : ℝ)| ≤ |(γ : ℝ)| ^ n := by
  rw [coeff_sqrtFactorSeries]
  push_cast
  rw [abs_mul, abs_pow]
  have hc : |(RungeCoefficients.halfChoose n : ℝ)| ≤ 1 := by
    exact_mod_cast RungeCoefficients.abs_halfChoose_le_one n
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg (abs_nonneg (γ : ℝ)) n)).trans_eq (one_mul _)

theorem factor_term_bound (γ : ℤ) (t : ℝ) (n : ℕ) :
    ‖term (sqrtFactorSeries γ) t n‖ ≤ |(γ : ℝ) * t| ^ n := by
  simp only [term, norm_mul, Real.norm_eq_abs, abs_pow]
  exact (mul_le_mul_of_nonneg_right (factor_coefficient_bound γ n) (pow_nonneg (abs_nonneg t) n)).trans_eq
    (by rw [abs_mul, mul_pow])

theorem factor_summable (γ : ℤ) (t : ℝ) (hsmall : |(γ : ℝ) * t| < 1) :
    AbsolutelySummable (sqrtFactorSeries γ) t := by
  have hgeo := summable_geometric_of_lt_one (abs_nonneg ((γ : ℝ) * t)) hsmall
  exact hgeo.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (factor_term_bound γ t)

theorem factor_value_square (γ : ℤ) (t : ℝ) (hsmall : |(γ : ℝ) * t| < 1) :
    value (sqrtFactorSeries γ) t ^ 2 = 1 + (γ : ℝ) * t := by
  have hf := factor_summable γ t hsmall
  have hone : AbsolutelySummable (1 : PowerSeries ℚ) t := by
    simpa only [map_one] using absolutelySummable_C 1 t
  have hvone : value (1 : PowerSeries ℚ) t = 1 := by
    simpa only [map_one, Rat.cast_one] using value_C 1 t
  have hsq : sqrtFactorSeries γ * sqrtFactorSeries γ = 1 + PowerSeries.C (γ : ℚ) * PowerSeries.X := by
    simpa only [pow_two] using sqrtFactorSeries_sq γ
  calc
    _ = value (sqrtFactorSeries γ * sqrtFactorSeries γ) t := by rw [value_mul _ _ t hf hf, pow_two]
    _ = value (1 + PowerSeries.C (γ : ℚ) * PowerSeries.X) t := by rw [hsq]
    _ = _ := by
      rw [value_add _ _ t hone (absolutelySummable_mul _ _ t (absolutelySummable_C (γ : ℚ) t) (absolutelySummable_X t)),
        value_mul _ _ t (absolutelySummable_C (γ : ℚ) t) (absolutelySummable_X t), value_C, value_X, hvone]
      norm_cast

theorem factor_value_positive (γ : ℤ) (t : ℝ) (hsmall : |(γ : ℝ) * t| ≤ 1 / 4) :
    0 < value (sqrtFactorSeries γ) t := by
  have hr : |(γ : ℝ) * t| < 1 := by linarith
  have hc : PowerSeries.coeff 0 (sqrtFactorSeries γ) = 1 := by simp [coeff_sqrtFactorSeries, RungeCoefficients.halfChoose]
  have ht := RealSeriesTail.constant_tail (sqrtFactorSeries γ) t |(γ : ℝ) * t|
    (abs_nonneg _) hr hc (factor_term_bound γ t)
  have hhalf : |(γ : ℝ) * t| / (1 - |(γ : ℝ) * t|) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - |(γ : ℝ) * t|)).mpr
    linarith
  have hh := (abs_le.mp (ht.trans hhalf)).1
  linarith

theorem product_summable {d : ℕ} (γ : Fin d → ℤ) (t : ℝ)
    (hsmall : ∀ i, |(γ i : ℝ) * t| < 1) : AbsolutelySummable (rungeProductSeries γ) t := by
  exact absolutelySummable_prod univ _ t (fun i _ ↦ factor_summable (γ i) t (hsmall i))

theorem product_value_square {d : ℕ} (γ : Fin d → ℤ) (t : ℝ)
    (hsmall : ∀ i, |(γ i : ℝ) * t| < 1) :
    value (rungeProductSeries γ) t ^ 2 = ∏ i, (1 + (γ i : ℝ) * t) := by
  rw [rungeProductSeries, value_prod univ _ t (fun i _ ↦ factor_summable (γ i) t (hsmall i)), ← prod_pow]
  apply prod_congr rfl
  intro i _
  exact factor_value_square (γ i) t (hsmall i)

theorem product_value_positive {d : ℕ} (γ : Fin d → ℤ) (t : ℝ)
    (hsmall : ∀ i, |(γ i : ℝ) * t| ≤ 1 / 4) : 0 < value (rungeProductSeries γ) t := by
  rw [rungeProductSeries, value_prod univ _ t (fun i _ ↦ factor_summable (γ i) t (by have h := hsmall i; linarith))]
  exact prod_pos (fun i _ ↦ factor_value_positive (γ i) t (hsmall i))

theorem scaled_product_square {r : ℕ} (γ : Fin (2 * r) → ℤ) (x : ℝ) (hx : x ≠ 0)
    (hsmall : ∀ i, |(γ i : ℝ) * (1 / x)| < 1) :
    (x ^ r * value (rungeProductSeries γ) (1 / x)) ^ 2 = ∏ i, (x + (γ i : ℝ)) := by
  rw [mul_pow, product_value_square γ (1 / x) hsmall, ← pow_mul]
  have hp : x ^ (r * 2) = ∏ _i : Fin (2 * r), x := by
    simp only [prod_const, card_univ, Fintype.card_fin]
    congr 1
    omega
  rw [hp, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  field_simp

theorem scaled_product_positive {r : ℕ} (γ : Fin (2 * r) → ℤ) (x : ℝ) (hx : 0 < x)
    (hsmall : ∀ i, |(γ i : ℝ) * (1 / x)| ≤ 1 / 4) :
    0 < x ^ r * value (rungeProductSeries γ) (1 / x) :=
  mul_pos (pow_pos hx r) (product_value_positive γ (1 / x) hsmall)

theorem small_parameter (γ : ℤ) (B : ℕ) (x : ℝ) (hx : 0 < x)
    (hB : 4 * (B : ℝ) ≤ x) (hγ : |γ| ≤ (B : ℤ)) : |(γ : ℝ) * (1 / x)| ≤ 1 / 4 := by
  have hγR : |(γ : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hγ
  rw [abs_mul, abs_div, abs_one, abs_of_pos hx, one_div, ← div_eq_mul_inv]
  apply (div_le_iff₀ hx).mpr
  linarith

end PaperP1.RungeSeriesValues
