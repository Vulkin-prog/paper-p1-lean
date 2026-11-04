module

public import PaperP1.Analysis.DeterminantDegreeChoice
public import PaperP1.Analysis.DeterminantLogScale

/-! # Exact column and row logarithmic costs on the complete monomial rectangle -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantDenominatorBudget

open Finset PaperP1.DeterminantIntegerRows

theorem sum_first_exponents (A B : ℕ) :
    (∑ i : Exponent A B, (i.1.val : ℝ)) = (((A + 1) * (B + 1) : ℕ) : ℝ) * A / 2 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun a : ℕ ↦ (a : ℝ)),
    WeightedLatticeTriangle.sum_first_coordinates]
  push_cast
  ring

theorem sum_second_exponents (A B : ℕ) :
    (∑ i : Exponent A B, (i.2.val : ℝ)) = (((A + 1) * (B + 1) : ℕ) : ℝ) * B / 2 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ ↦ (b : ℝ)),
    WeightedLatticeTriangle.sum_first_coordinates]
  push_cast
  ring

theorem column_product_positive (A B : ℕ) {s₀ t₀ : ℝ} (hs₀ : 0 < s₀) (ht₀ : 0 < t₀) :
    0 < ∏ i : Exponent A B, s₀ ^ i.1.val * t₀ ^ i.2.val := by
  exact prod_pos (fun i _ ↦ mul_pos (pow_pos hs₀ _) (pow_pos ht₀ _))

theorem column_log_cost (A B : ℕ) {s₀ t₀ : ℝ} (hs₀ : 0 < s₀) (ht₀ : 0 < t₀) :
    Real.log (∏ i : Exponent A B, s₀ ^ i.1.val * t₀ ^ i.2.val) =
      (((A + 1) * (B + 1) : ℕ) : ℝ) *
        ((A : ℝ) / 2 * Real.log s₀ + (B : ℝ) / 2 * Real.log t₀) := by
  rw [Real.log_prod (fun i _ ↦ (mul_pos (pow_pos hs₀ _) (pow_pos ht₀ _)).ne')]
  simp_rw [Real.log_mul (pow_ne_zero _ hs₀.ne') (pow_ne_zero _ ht₀.ne'), Real.log_pow]
  rw [sum_add_distrib, ← sum_mul, ← sum_mul, sum_first_exponents, sum_second_exponents]
  ring

theorem column_product (A B : ℕ) {s₀ t₀ : ℝ} (hs₀ : 0 < s₀) (ht₀ : 0 < t₀) :
    (∏ i : Exponent A B, s₀ ^ i.1.val * t₀ ^ i.2.val) =
      Real.exp ((((A + 1) * (B + 1) : ℕ) : ℝ) *
        ((A : ℝ) / 2 * Real.log s₀ + (B : ℝ) / 2 * Real.log t₀)) := by
  rw [← column_log_cost A B hs₀ ht₀, Real.exp_log (column_product_positive A B hs₀ ht₀)]

theorem row_product_bound {ι : Type*} [Fintype ι] (A B : ℕ) (e u : ι → ℝ)
    {E U : ℝ} (hE : 0 < E) (hU : 0 < U)
    (he₀ : ∀ i, 0 ≤ e i) (hu₀ : ∀ i, 0 ≤ u i)
    (he : ∀ i, e i ≤ E) (hu : ∀ i, u i ≤ U) :
    (∏ i, e i ^ A * u i ^ B) ≤
      Real.exp ((Fintype.card ι : ℝ) * ((A : ℝ) * Real.log E + (B : ℝ) * Real.log U)) := by
  calc
    _ ≤ ∏ _i : ι, E ^ A * U ^ B := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (pow_nonneg (he₀ i) _) (pow_nonneg (hu₀ i) _)
      · intro i _
        exact mul_le_mul (pow_le_pow_left₀ (he₀ i) (he i) A)
          (pow_le_pow_left₀ (hu₀ i) (hu i) B) (pow_nonneg (hu₀ i) _) (pow_nonneg hE.le _)
    _ = (E ^ A * U ^ B) ^ Fintype.card ι := by simp only [prod_const, card_univ]
    _ = _ := by
      rw [← Real.exp_log (pow_pos (mul_pos (pow_pos hE A) (pow_pos hU B)) _)]
      congr 1
      rw [Real.log_pow, Real.log_mul (pow_ne_zero A hE.ne') (pow_ne_zero B hU.ne'), Real.log_pow, Real.log_pow]

theorem normalized_denominator_cost {E U s₀ t₀ : ℝ}
    (hE : 0 < E) (hU : 0 < U) (hs₀ : 0 < s₀) (ht₀ : 0 < t₀) (A B : ℕ) :
    (A : ℝ) * Real.log E + (B : ℝ) * Real.log U +
      ((A : ℝ) / 2 * Real.log s₀ + (B : ℝ) / 2 * Real.log t₀) =
        ((A : ℝ) * Real.log (E ^ 2 * s₀) + (B : ℝ) * Real.log (U ^ 2 * t₀)) / 2 := by
  rw [Real.log_mul (pow_ne_zero 2 hE.ne') hs₀.ne',
    Real.log_mul (pow_ne_zero 2 hU.ne') ht₀.ne', Real.log_pow, Real.log_pow]
  ring

theorem total_product_bound (A B : ℕ) (e u : Exponent A B → ℝ)
    {E U s₀ t₀ : ℝ} (hE : 0 < E) (hU : 0 < U) (hs₀ : 0 < s₀) (ht₀ : 0 < t₀)
    (he₀ : ∀ i, 0 ≤ e i) (hu₀ : ∀ i, 0 ≤ u i)
    (he : ∀ i, e i ≤ E) (hu : ∀ i, u i ≤ U) :
    (∏ i, e i ^ A * u i ^ B) * (∏ j : Exponent A B, s₀ ^ j.1.val * t₀ ^ j.2.val) ≤
      Real.exp ((((A + 1) * (B + 1) : ℕ) : ℝ) *
        (((A : ℝ) * Real.log (E ^ 2 * s₀) + (B : ℝ) * Real.log (U ^ 2 * t₀)) / 2)) := by
  have h := mul_le_mul_of_nonneg_right (row_product_bound A B e u hE hU he₀ hu₀ he hu)
    (column_product_positive A B hs₀ ht₀).le
  simp only [Exponent, Fintype.card_prod, Fintype.card_fin] at h
  rw [column_product A B hs₀ ht₀, ← Real.exp_add, ← mul_add,
    normalized_denominator_cost hE hU hs₀ ht₀ A B] at h
  rw [column_product A B hs₀ ht₀]
  exact h

end PaperP1.DeterminantDenominatorBudget
