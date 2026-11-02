module

public import PaperP1.Probability.CompletedBinomial

/-! # An explicit finite Poisson–Charlier conversion for actual signed laws

This is the analytic step of companion T17.4, with the covariance parameter
kept explicit. Its arithmetic asymptotic bound is a separate obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePoissonCharlierConversion

open PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.CompletedBinomial

def finiteReference (n : ℕ) (p β : ℝ) : SignedLaw ℝ :=
  (bernoulli p) ^ n + scalar β * forwardDifference ^ 2 * (bernoulli p) ^ (n - 2)

def completedReference (n : ℕ) (p β : ℝ) : Space :=
  binomial n p + β • (delta ^ 2 * binomial (n - 2) p)

theorem ofFinite_scalar_mul (c : ℝ) (ν : SignedLaw ℝ) :
    ofFinite (scalar c * ν) = c • ofFinite ν := by
  rw [map_mul]
  change algebraMap ℝ Space c * ofFinite ν = c • ofFinite ν
  rw [Algebra.smul_def]

theorem ofFinite_reference (n : ℕ) (p β : ℝ) :
    ofFinite (finiteReference n p β) = completedReference n p β := by
  rw [finiteReference, map_add, mul_assoc, ofFinite_scalar_mul, map_mul]
  simp only [map_pow]
  simp only [completedReference, binomial, map_pow, delta]

theorem coeff_completedReference (n : ℕ) (p β : ℝ) (k : ℕ) :
    coeff k (completedReference n p β) = (finiteReference n p β).coeff k := by
  rw [← ofFinite_reference, coeff_ofFinite]

theorem norm_delta_squared_le : ‖delta ^ 2‖ ≤ 4 := by
  calc
    _ ≤ ‖delta‖ ^ 2 := norm_pow_le delta 2
    _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) norm_delta_le 2
    _ = 4 := by norm_num

theorem norm_conversion {n : ℕ} (hn : 2 ≤ n) {p A : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hmean : (n : ℝ) * p ≤ A) (β c₂ : ℝ) :
    ‖completedReference n p β - quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)‖ ≤
      4 * |β - c₂| +
        16 * Real.exp (2 * A + 4) * ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2) +
        16 * Real.exp (2 * A + 2) * |c₂| * (p + (n : ℝ) * p ^ 2) := by
  have hproduct : ‖delta ^ 2 * binomial (n - 2) p‖ ≤ 4 := by
    exact (norm_mul_le _ _).trans (by simpa only [mul_one] using (mul_le_mul
      norm_delta_squared_le (norm_binomial_le_one (n - 2) hp hp₁)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)))
  have hfirst : ‖(β - c₂) • (delta ^ 2 * binomial (n - 2) p)‖ ≤ 4 * |β - c₂| := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith only [mul_le_mul_of_nonneg_left hproduct (abs_nonneg (β - c₂))]
  have hthird : ‖c₂ • (delta ^ 2 * (binomial (n - 2) p - poisson ((n : ℝ) * p)))‖ ≤
      16 * Real.exp (2 * A + 2) * |c₂| * (p + (n : ℝ) * p ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |c₂| * (‖delta ^ 2‖ * ‖binomial (n - 2) p - poisson ((n : ℝ) * p)‖) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ |c₂| * (4 * (4 * (p + (n : ℝ) * p ^ 2) * Real.exp (2 * A + 2))) := by
        gcongr
        · exact norm_delta_squared_le
        · exact two_deleted_error hn hp hp₁ hmean
      _ = _ := by ring
  have hid : completedReference n p β - quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2) =
      ((β - c₂) • (delta ^ 2 * binomial (n - 2) p) +
        (binomial n p - quadratic ((n : ℝ) * p) (-((n : ℝ) * p ^ 2)))) +
      c₂ • (delta ^ 2 * (binomial (n - 2) p - poisson ((n : ℝ) * p))) := by
    dsimp only [completedReference, quadratic]
    simp only [mul_sub]
    module
  rw [hid]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add hfirst (quadratic_error n hp hp₁ hmean)) hthird)

theorem coefficient_conversion {n : ℕ} (hn : 2 ≤ n) {p A : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hmean : (n : ℝ) * p ≤ A) (β c₂ : ℝ) :
    (∑' k : ℕ, |(finiteReference n p β).coeff k -
      PoissonSequence.quadraticMass ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2) k|) ≤
      4 * |β - c₂| +
        16 * Real.exp (2 * A + 4) * ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2) +
        16 * Real.exp (2 * A + 2) * |c₂| * (p + (n : ℝ) * p ^ 2) := by
  have h := (tsum_abs_coeff_le
    (completedReference n p β - quadratic ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2))).trans
      (norm_conversion hn hp hp₁ hmean β c₂)
  simpa only [map_sub, coeff_completedReference, coeff_quadratic] using h

theorem actual_signed_measure_conversion {n : ℕ} (hn : 2 ≤ n) {p A : ℝ}
    (hp : 0 ≤ p) (hp₁ : p ≤ 1) (hmean : (n : ℝ) * p ≤ A) (β c₂ : ℝ) :
    (∑' k : ℕ, |(FiniteLawEmbedding.embed (finiteReference n p β) -
      QuadraticPoisson.reference ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2)) {k}|) ≤
      4 * |β - c₂| +
        16 * Real.exp (2 * A + 4) * ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2) +
        16 * Real.exp (2 * A + 2) * |c₂| * (p + (n : ℝ) * p ^ 2) := by
  have href (k : ℕ) : QuadraticPoisson.reference ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2) {k} =
      PoissonSequence.quadraticMass ((n : ℝ) * p) (2 * c₂ - (n : ℝ) * p ^ 2) k :=
    AtomicSignedLaw.ofSequence_singleton
      (PoissonSequence.hasSum_quadraticMass _ _ (mul_nonneg (Nat.cast_nonneg n) hp)).summable k
  simpa only [_root_.sub_apply, FiniteLawEmbedding.embed_singleton, href] using
    coefficient_conversion hn hp hp₁ hmean β c₂

end PaperP1.FinitePoissonCharlierConversion
