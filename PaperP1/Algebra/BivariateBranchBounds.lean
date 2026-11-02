module

public import PaperP1.Arithmetic.BiquadraticNumeratorFactor
public import PaperP1.Algebra.BivariateRungeCoefficients

/-! # Uniform geometric coefficient bounds for actual shifted reciprocal word branches -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateBranchBounds

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateReciprocalSeries
  PaperP1.BivariateReciprocalProduct PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticNumeratorFactor

theorem shift_branch_bound {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (B : ℕ) (hB : 1 ≤ B) (hγ : ∀ i, |γ i| ≤ (B : ℤ)) (hδ : ∀ i, |δ i| ≤ (B : ℤ))
    (sx sy a b : ℕ) :
    |coefficient a b (shift sx sy (branch γ δ))| ≤
      (2 : ℚ) ^ (d + e) * (2 * (B : ℚ)) ^ (a + b) := by
  rw [coefficient_shift]
  split_ifs with hab
  · rw [coefficient_branch]
    have hp := BivariateRungeCoefficients.product_bound γ δ (a - sx) (b - sy) (B : ℚ)
      (by positivity) (fun i ↦ by exact_mod_cast hγ i) (fun i ↦ by exact_mod_cast hδ i)
    calc
      _ ≤ (2 : ℚ) ^ ((a - sx) + (b - sy) + d + e) * (B : ℚ) ^ ((a - sx) + (b - sy)) := hp
      _ = (2 : ℚ) ^ (d + e) * (2 * (B : ℚ)) ^ ((a - sx) + (b - sy)) := by
        simp only [pow_add, mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 2 * B)) (by omega)) (by positivity)
  · simp only [abs_zero]
    positivity

theorem rational_coefficient_height (P : ℤ[X][X]) (H : ℕ) (hH : BivariateHeight.height P ≤ H)
    (x y : ℕ) : |((P.coeff y).coeff x : ℚ)| ≤ (H : ℚ) := by
  have hn := (BivariateHeight.coefficient_natAbs_le_height P y x).trans hH
  have hz : |(P.coeff y).coeff x| ≤ (H : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hn
  exact_mod_cast hz

theorem reciprocal_branch_bound {d e : ℕ} (γ : Fin d → ℤ) (δ : Fin e → ℤ)
    (P : ℤ[X][X]) (kx ky H B : ℕ) (hx : degreeX P ≤ kx) (hy : degreeY P ≤ ky)
    (hH : BivariateHeight.height P ≤ H) (hB : 1 ≤ B)
    (hγ : ∀ i, |γ i| ≤ (B : ℤ)) (hδ : ∀ i, |δ i| ≤ (B : ℤ)) (a b : ℕ) :
    |coefficient a b (reciprocal P kx ky * branch γ δ)| ≤
      (((kx + 1) * (ky + 1) : ℕ) : ℚ) * (H : ℚ) * (2 : ℚ) ^ (d + e) * (2 * (B : ℚ)) ^ (a + b) := by
  have hrep : reciprocal P kx ky * branch γ δ =
      ∑ i : Fin (kx + 1) × Fin (ky + 1),
        PowerSeries.C (PowerSeries.C ((P.coeff i.2.val).coeff i.1.val : ℚ)) *
          shift (kx - i.1.val) (ky - i.2.val) (branch γ δ) := by
    conv_lhs => rw [← rectangle_reconstruction P kx ky hx hy]
    exact reciprocal_rectangle_mul kx ky _ _
  rw [hrep, coefficient_sum]
  calc
    _ ≤ ∑ i : Fin (kx + 1) × Fin (ky + 1),
        |coefficient a b (PowerSeries.C (PowerSeries.C ((P.coeff i.2.val).coeff i.1.val : ℚ)) *
          shift (kx - i.1.val) (ky - i.2.val) (branch γ δ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (kx + 1) × Fin (ky + 1),
        (H : ℚ) * ((2 : ℚ) ^ (d + e) * (2 * (B : ℚ)) ^ (a + b)) := by
      apply sum_le_sum
      intro i _
      rw [coefficient_scalar, abs_mul]
      exact mul_le_mul (rational_coefficient_height P H hH i.1.val i.2.val)
        (shift_branch_bound γ δ B hB hγ hδ _ _ a b) (abs_nonneg _) (by positivity)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod, Fintype.card_fin]
      ring

end PaperP1.BivariateBranchBounds
