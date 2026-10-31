module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Coefficient and leading-coordinate bounds for specialization

The last inequality remains valid when specialization drops the degree of
either factor. This avoids exceptional specializations in the bivariate
factor-height argument: a coefficient at a fixed upper degree may be zero.
All Mahler and Parseval facts used here are proved Mathlib theorems.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MahlerCoefficientBounds

open Polynomial Finset

def coefficientEnergy (p : ℂ[X]) : ℝ := ∑ i ∈ p.support, ‖p.coeff i‖ ^ 2

def l2CoefficientNorm (p : ℂ[X]) : ℝ := Real.sqrt (coefficientEnergy p)

theorem coefficientEnergy_nonneg (p : ℂ[X]) : 0 ≤ coefficientEnergy p :=
  sum_nonneg fun _ _ ↦ sq_nonneg _

theorem l2CoefficientNorm_nonneg (p : ℂ[X]) : 0 ≤ l2CoefficientNorm p := Real.sqrt_nonneg _

theorem l2CoefficientNorm_sq (p : ℂ[X]) : (l2CoefficientNorm p) ^ 2 = coefficientEnergy p :=
  Real.sq_sqrt (coefficientEnergy_nonneg p)

theorem coefficientEnergy_le_card_mul_sq (p : ℂ[X]) (H : ℝ)
    (hcoeff : ∀ n, ‖p.coeff n‖ ≤ H) :
    coefficientEnergy p ≤ (p.support.card : ℝ) * H ^ 2 := by
  calc
    _ ≤ ∑ _i ∈ p.support, H ^ 2 :=
      sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hcoeff i) 2
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem mahler_le_l2 (p : ℂ[X]) : p.mahlerMeasure ≤ l2CoefficientNorm p :=
  p.mahlerMeasure_le_sqrt_sum_sq_norm_coeff

theorem norm_coeff_le_choose_mul_mahler_of_degree_bound
    (p : ℂ[X]) (D n : ℕ) (hD : p.natDegree ≤ D) :
    ‖p.coeff n‖ ≤ (D.choose n : ℝ) * p.mahlerMeasure := by
  apply (p.norm_coeff_le_choose_mul_mahlerMeasure n).trans
  apply mul_le_mul_of_nonneg_right _ p.mahlerMeasure_nonneg
  exact_mod_cast Nat.choose_le_choose n hD

theorem norm_top_coeff_le_mahler (p : ℂ[X]) (D : ℕ) (hD : p.natDegree ≤ D) :
    ‖p.coeff D‖ ≤ p.mahlerMeasure := by
  simpa only [Nat.choose_self, Nat.cast_one, one_mul] using
    norm_coeff_le_choose_mul_mahler_of_degree_bound p D D hD

theorem factor_coefficient_product_bound (g h : ℂ[X]) (D E n : ℕ)
    (hg : g.natDegree ≤ D) (hh : h.natDegree ≤ E) :
    ‖g.coeff n * h.coeff E‖ ≤ (D.choose n : ℝ) * l2CoefficientNorm (g * h) := by
  have hgcoeff := norm_coeff_le_choose_mul_mahler_of_degree_bound g D n hg
  have hhcoeff := norm_top_coeff_le_mahler h E hh
  calc
    _ = ‖g.coeff n‖ * ‖h.coeff E‖ := norm_mul _ _
    _ ≤ ((D.choose n : ℝ) * g.mahlerMeasure) * h.mahlerMeasure :=
      mul_le_mul hgcoeff hhcoeff (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) g.mahlerMeasure_nonneg)
    _ = (D.choose n : ℝ) * (g * h).mahlerMeasure := by rw [mahlerMeasure_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mahler_le_l2 _) (Nat.cast_nonneg _)

theorem factor_coefficient_product_bound_two_pow (g h : ℂ[X]) (D E n : ℕ)
    (hg : g.natDegree ≤ D) (hh : h.natDegree ≤ E) :
    ‖g.coeff n * h.coeff E‖ ≤ (2 : ℝ) ^ D * l2CoefficientNorm (g * h) := by
  apply (factor_coefficient_product_bound g h D E n hg hh).trans
  apply mul_le_mul_of_nonneg_right _ (l2CoefficientNorm_nonneg _)
  exact_mod_cast Nat.choose_le_two_pow D n

end PaperP1.MahlerCoefficientBounds
