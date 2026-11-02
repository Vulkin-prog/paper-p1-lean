module

public import PaperP1.Analysis.WeightedGeometricTail
public import PaperP1.Analysis.RungeSeriesValues
public import PaperP1.Arithmetic.BiquadraticFormalNumerator

/-! # Actual bivariate real values by total degree and their vanishing-tail estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateSeriesValue

open Finset PaperP1.BiquadraticFormalNumerator PaperP1.RungePowerSeries

def term (f : Series) (ξ η : ℝ) (a b : ℕ) : ℝ := (coefficient a b f : ℝ) * ξ ^ a * η ^ b

def diagonal (f : Series) (ξ η : ℝ) (n : ℕ) : ℝ := ∑ p ∈ Finset.antidiagonal n, term f ξ η p.1 p.2

def value (f : Series) (ξ η : ℝ) : ℝ := ∑' n, diagonal f ξ η n

def AbsolutelySummable (f : Series) (ξ η : ℝ) : Prop := Summable (fun n ↦ ‖diagonal f ξ η n‖)

theorem term_add (f g : Series) (ξ η : ℝ) (a b : ℕ) :
    term (f + g) ξ η a b = term f ξ η a b + term g ξ η a b := by
  simp only [term, coefficient, map_add, Rat.cast_add, add_mul]

theorem diagonal_add (f g : Series) (ξ η : ℝ) (n : ℕ) :
    diagonal (f + g) ξ η n = diagonal f ξ η n + diagonal g ξ η n := by
  simp only [diagonal, term_add, sum_add_distrib]

theorem value_add (f g : Series) (ξ η : ℝ)
    (hf : AbsolutelySummable f ξ η) (hg : AbsolutelySummable g ξ η) :
    value (f + g) ξ η = value f ξ η + value g ξ η := by
  unfold value
  simp only [diagonal_add]
  exact hf.of_norm.tsum_add hg.of_norm

theorem diagonal_scalar (c : ℚ) (f : Series) (ξ η : ℝ) (n : ℕ) :
    diagonal (PowerSeries.C (PowerSeries.C c) * f) ξ η n = (c : ℝ) * diagonal f ξ η n := by
  unfold diagonal
  rw [mul_sum]
  apply sum_congr rfl
  intro p _
  simp only [term, coefficient_scalar, Rat.cast_mul]
  ring

theorem value_scalar (c : ℚ) (f : Series) (ξ η : ℝ) :
    value (PowerSeries.C (PowerSeries.C c) * f) ξ η = (c : ℝ) * value f ξ η := by
  unfold value
  simp only [diagonal_scalar]
  exact tsum_mul_left

theorem diagonal_branch {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ) (ξ η : ℝ) (n : ℕ) :
    diagonal (branch γ δ) ξ η n = ∑ p ∈ Finset.antidiagonal n,
      RealSeriesEvaluation.term (rungeProductSeries γ) ξ p.1 *
        RealSeriesEvaluation.term (rungeProductSeries δ) η p.2 := by
  unfold diagonal
  apply sum_congr rfl
  intro p _
  simp only [term, coefficient_branch, RealSeriesEvaluation.term, coeff_rungeProductSeries, Rat.cast_mul]
  ring

theorem branch_summable {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ) (ξ η : ℝ)
    (hγ : ∀ i, |(γ i : ℝ) * ξ| < 1) (hδ : ∀ i, |(δ i : ℝ) * η| < 1) :
    AbsolutelySummable (branch γ δ) ξ η := by
  unfold AbsolutelySummable
  simp only [diagonal_branch]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm
    (RungeSeriesValues.product_summable γ ξ hγ) (RungeSeriesValues.product_summable δ η hδ)

theorem value_branch {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ) (ξ η : ℝ)
    (hγ : ∀ i, |(γ i : ℝ) * ξ| < 1) (hδ : ∀ i, |(δ i : ℝ) * η| < 1) :
    value (branch γ δ) ξ η = RealSeriesEvaluation.value (rungeProductSeries γ) ξ *
      RealSeriesEvaluation.value (rungeProductSeries δ) η := by
  unfold value RealSeriesEvaluation.value
  simp only [diagonal_branch]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (RungeSeriesValues.product_summable γ ξ hγ) (RungeSeriesValues.product_summable δ η hδ)).symm

theorem diagonal_geometric_bound (f : Series) (ξ η C R t : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ht : 0 ≤ t) (hξ : |ξ| ≤ t) (hη : |η| ≤ t)
    (hcoeff : ∀ a b, |(coefficient a b f : ℝ)| ≤ C * R ^ (a + b)) (n : ℕ) :
    ‖diagonal f ξ η n‖ ≤ C * ((n : ℝ) + 1) * (R * t) ^ n := by
  have hterm : ∀ p ∈ Finset.antidiagonal n, ‖term f ξ η p.1 p.2‖ ≤ C * (R * t) ^ n := by
    intro p hp
    have hn := Finset.mem_antidiagonal.mp hp
    have hweights : |ξ| ^ p.1 * |η| ^ p.2 ≤ t ^ (p.1 + p.2) := by
      rw [pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg ξ) hξ _) (pow_le_pow_left₀ (abs_nonneg η) hη _)
        (pow_nonneg (abs_nonneg η) _) (pow_nonneg ht _)
    calc
      ‖term f ξ η p.1 p.2‖ = |(coefficient p.1 p.2 f : ℝ)| * (|ξ| ^ p.1 * |η| ^ p.2) := by
        simp only [term, norm_mul, Real.norm_eq_abs, abs_pow]
        ring
      _ ≤ (C * R ^ (p.1 + p.2)) * t ^ (p.1 + p.2) :=
        mul_le_mul (hcoeff _ _) hweights (mul_nonneg (pow_nonneg (abs_nonneg ξ) _) (pow_nonneg (abs_nonneg η) _))
          (mul_nonneg hC (pow_nonneg hR _))
      _ = C * (R * t) ^ n := by rw [mul_assoc, ← mul_pow, hn]
  calc
    _ ≤ ∑ p ∈ Finset.antidiagonal n, ‖term f ξ η p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.antidiagonal n, C * (R * t) ^ n := sum_le_sum hterm
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal, Nat.cast_add, Nat.cast_one]
      ring

theorem geometric_summability (f : Series) (ξ η C R t : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ht : 0 ≤ t) (hξ : |ξ| ≤ t) (hη : |η| ≤ t)
    (hsmall : R * t < 1) (hcoeff : ∀ a b, |(coefficient a b f : ℝ)| ≤ C * R ^ (a + b)) :
    AbsolutelySummable f ξ η := by
  have hmajorant : Summable (fun n : ℕ ↦ C * ((n : ℝ) + 1) * (R * t) ^ n) := by
    simpa only [mul_assoc] using (WeightedGeometricTail.weighted_hasSum (R * t) (mul_nonneg hR ht) hsmall).summable.mul_left C
  exact hmajorant.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (diagonal_geometric_bound f ξ η C R t hC hR ht hξ hη hcoeff)

theorem vanishing_tail_bound (f : Series) (ξ η C R t : ℝ) (M : ℕ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ht : 0 ≤ t) (hξ : |ξ| ≤ t) (hη : |η| ≤ t)
    (hsmall : R * t ≤ 1 / 4) (hcoeff : ∀ a b, |(coefficient a b f : ℝ)| ≤ C * R ^ (a + b))
    (hzero : ∀ a b, a + b < M → coefficient a b f = 0) :
    ‖value f ξ η‖ ≤ 2 * C * ((M : ℝ) + 1) * (R * t) ^ M := by
  apply WeightedGeometricTail.vanishing_tail_bound (diagonal f ξ η) C (R * t) M hC
    (mul_nonneg hR ht) hsmall (diagonal_geometric_bound f ξ η C R t hC hR ht hξ hη hcoeff)
  intro n hn
  apply sum_eq_zero
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  simp only [term, hzero p.1 p.2 (by omega), Rat.cast_zero, zero_mul]

end PaperP1.BivariateSeriesValue
