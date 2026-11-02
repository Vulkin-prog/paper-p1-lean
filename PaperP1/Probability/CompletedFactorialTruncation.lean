module

public import PaperP1.Probability.FactorialCountTruncation
public import PaperP1.Probability.CompletedLawShift
public import PaperP1.Analysis.BanachFactorialRemainder

/-! # Actual count-law reconstruction and a factorial Poisson remainder in ordinary l1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedFactorialTruncation

open Finset PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.FactorialCountTruncation

theorem polynomial_eq (a : ℕ → ℝ) (k : ℕ) :
    ofFinite (polynomial a k) = ∑ r ∈ range k, (a r / (r.factorial : ℝ)) • delta ^ r := by
  rw [polynomial, map_sum]
  apply sum_congr rfl
  intro r _
  rw [map_mul, map_pow]
  change algebraMap ℝ Space (a r / (r.factorial : ℝ)) * delta ^ r = _
  rw [Algebra.smul_def]

theorem poisson_partial_eq (μ : ℝ) (k : ℕ) :
    ofFinite (polynomial (fun r ↦ μ ^ r) k) =
      ∑ r ∈ range k, ((r.factorial : ℝ)⁻¹) • (μ • delta) ^ r := by
  rw [polynomial_eq]
  apply sum_congr rfl
  intro r _
  rw [smul_pow, smul_smul]
  congr 1
  ring

theorem poisson_remainder (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    ‖poisson μ - ofFinite (polynomial (fun r ↦ μ ^ r) k)‖ ≤
      (2 * μ) ^ k / (k.factorial : ℝ) * Real.exp (2 * μ) := by
  have hx : ‖μ • delta‖ ≤ 2 * μ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
    nlinarith only [mul_le_mul_of_nonneg_left norm_delta_le hμ]
  rw [poisson_partial_eq]
  exact (BanachFactorialRemainder.norm_exp_sub_partial_le (μ • delta) k).trans
    (mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx k) (by positivity))
      (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by positivity))

theorem count_distance_bound {Ω ι : Type*} [Fintype Ω] [LinearOrder ι]
    (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (hk : 1 ≤ k) :
    ‖ofFinite (countLaw G P.weight J) - poisson μ‖ ≤
      (2 : ℝ) ^ k / (k.factorial : ℝ) * moment G P J k +
      (∑ r ∈ range k, (2 : ℝ) ^ r / (r.factorial : ℝ) * |moment G P J r - μ ^ r|) +
      (2 * μ) ^ k / (k.factorial : ℝ) * Real.exp (2 * μ) := by
  let A := ofFinite (polynomial (moment G P J) k)
  let B := ofFinite (polynomial (fun r ↦ μ ^ r) k)
  have h1 : ‖ofFinite (countLaw G P.weight J) - A‖ ≤
      (2 : ℝ) ^ k / (k.factorial : ℝ) * moment G P J k := by
    rw [← map_sub, norm_ofFinite]
    exact remainder_bound G P J k hk
  have h2 : ‖A - B‖ ≤ ∑ r ∈ range k, (2 : ℝ) ^ r / (r.factorial : ℝ) * |moment G P J r - μ ^ r| := by
    rw [← map_sub, norm_ofFinite]
    exact polynomial_difference _ _ k
  have h3 : ‖B - poisson μ‖ ≤ (2 * μ) ^ k / (k.factorial : ℝ) * Real.exp (2 * μ) := by
    rw [norm_sub_rev]
    exact poisson_remainder μ hμ k
  have ht1 := dist_triangle (ofFinite (countLaw G P.weight J)) A (poisson μ)
  have ht2 := dist_triangle A B (poisson μ)
  simp only [dist_eq_norm] at ht1 ht2
  linarith only [ht1, ht2, h1, h2, h3]

end PaperP1.CompletedFactorialTruncation
