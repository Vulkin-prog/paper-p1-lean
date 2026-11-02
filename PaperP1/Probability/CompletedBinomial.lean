module

public import PaperP1.Probability.CompletedLawShift
public import PaperP1.Analysis.BernoulliExponentialApproximation
public import Mathlib.Tactic.Module

/-! # Explicit finite binomial-to-Poisson error estimates in ordinary ℓ¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedBinomial

open PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.BanachExponentialRemainder
  PaperP1.BanachPowerPerturbation PaperP1.BernoulliExponentialApproximation

def binomial (n : ℕ) (p : ℝ) : Space := ofFinite ((bernoulli p) ^ n)

theorem bernoulli_eq (p : ℝ) : ofFinite (bernoulli p) = 1 + p • delta := by
  rw [bernoulli, map_add, atom_zero, map_one, map_mul]
  change 1 + algebraMap ℝ Space p * delta = 1 + p • delta
  rw [Algebra.smul_def]

theorem poisson_nat_mul (n : ℕ) (p : ℝ) :
    poisson ((n : ℝ) * p) = (NormedSpace.exp (p • delta)) ^ n := by
  rw [poisson, ← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

theorem norm_binomial_le_one (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    ‖binomial n p‖ ≤ 1 := by
  have hb : ‖ofFinite (bernoulli p)‖ = 1 := by
    rw [norm_ofFinite]
    exact l1Norm_probability (bernoulli_isProbability hp hp₁)
  simpa only [binomial, map_pow, hb, one_pow] using norm_pow_le (ofFinite (bernoulli p)) n

theorem norm_parameter_le {p : ℝ} (hp : 0 ≤ p) : ‖p • delta‖ ≤ 2 * p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  nlinarith only [mul_le_mul_of_nonneg_left norm_delta_le hp]

theorem first_order_error (n : ℕ) {p A : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hmean : (n : ℝ) * p ≤ A) :
    ‖binomial n p - poisson ((n : ℝ) * p)‖ ≤
      4 * (n : ℝ) * p ^ 2 * Real.exp (2 * A + 2) := by
  let v := p • delta
  let M := Real.exp ‖v‖
  have hM : 1 ≤ M := Real.one_le_exp (norm_nonneg v)
  have hx : ‖1 + v‖ ≤ M := by
    calc
      _ ≤ 1 + ‖v‖ := by simpa only [norm_one] using norm_add_le (1 : Space) v
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp ‖v‖
  have hy : ‖NormedSpace.exp v‖ ≤ M := norm_exp_le v
  have he : ‖1 + v - NormedSpace.exp v‖ ≤ ‖v‖ ^ 2 * M := by
    rw [norm_sub_rev]
    exact norm_exp_sub_linear_le v
  have hr : ‖v‖ ≤ 2 * p := norm_parameter_le hp
  have hexponent : ((n : ℝ) + 1) * ‖v‖ ≤ 2 * A + 2 := by
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ (n : ℝ) + 1)
    nlinarith only [hh, hmean, hp₁]
  rw [binomial, map_pow, bernoulli_eq, poisson_nat_mul]
  calc
    _ ≤ (n : ℝ) * M ^ n * ‖1 + v - NormedSpace.exp v‖ :=
      norm_pow_sub_le _ _ M hM hx hy n
    _ ≤ (n : ℝ) * M ^ n * (‖v‖ ^ 2 * M) := by gcongr
    _ = (n : ℝ) * ‖v‖ ^ 2 * Real.exp (((n : ℝ) + 1) * ‖v‖) := by
      rw [show (n : ℝ) * M ^ n * (‖v‖ ^ 2 * M) = (n : ℝ) * ‖v‖ ^ 2 * M ^ (n + 1) by rw [pow_succ]; ring]
      dsimp only [M]
      rw [← Real.exp_nat_mul]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ (n : ℝ) * (2 * p) ^ 2 * Real.exp (2 * A + 2) := by gcongr
    _ = _ := by ring

theorem quadratic_error (n : ℕ) {p A : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hmean : (n : ℝ) * p ≤ A) :
    ‖binomial n p - quadratic ((n : ℝ) * p) (-((n : ℝ) * p ^ 2))‖ ≤
      16 * Real.exp (2 * A + 4) * ((n : ℝ) * p ^ 3 + ((n : ℝ) * p ^ 2) ^ 2) := by
  let v := p • delta
  have hr : ‖v‖ ≤ 2 * p := norm_parameter_le hp
  have hexponent : ((n : ℝ) + 2) * ‖v‖ ≤ 2 * A + 4 := by
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ (n : ℝ) + 2)
    nlinarith only [hh, hmean, hp₁]
  have hcorrection : n • ((1 / 2 : ℝ) • (v ^ 2 * (NormedSpace.exp v) ^ n)) =
      ((n : ℝ) * p ^ 2 / 2) • (delta ^ 2 * (NormedSpace.exp v) ^ n) := by
    dsimp only [v]
    rw [smul_pow, smul_mul_assoc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
    congr 1
    ring
  have hid : binomial n p - quadratic ((n : ℝ) * p) (-((n : ℝ) * p ^ 2)) =
      (1 + v) ^ n - (NormedSpace.exp v) ^ n +
        n • ((1 / 2 : ℝ) • (v ^ 2 * (NormedSpace.exp v) ^ n)) := by
    rw [hcorrection, binomial, map_pow, bernoulli_eq, quadratic, poisson_nat_mul]
    simp only [neg_div, neg_smul]
    module
  rw [hid]
  calc
    _ ≤ (2 * (n : ℝ) * ‖v‖ ^ 3 + (n : ℝ) ^ 2 * ‖v‖ ^ 4) *
          Real.exp (((n : ℝ) + 2) * ‖v‖) := norm_quadratic_error v n
    _ ≤ (2 * (n : ℝ) * (2 * p) ^ 3 + (n : ℝ) ^ 2 * (2 * p) ^ 4) *
          Real.exp (2 * A + 4) := by gcongr
    _ = _ := by ring

theorem delete_two_error {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1) :
    ‖binomial (n - 2) p - binomial n p‖ ≤ 4 * p := by
  let b := ofFinite (bernoulli p)
  have hb : ‖b‖ ≤ 1 := by simpa only [binomial, pow_one] using norm_binomial_le_one 1 hp hp₁
  have hb1 : ‖1 - b‖ ≤ 2 * p := by
    have hbd : 1 - b = -(p • delta) := by
      dsimp only [b]
      rw [bernoulli_eq]
      abel
    rw [hbd, norm_neg]
    exact norm_parameter_le hp
  have hb2 : ‖1 - b ^ 2‖ ≤ 4 * p := by
    have hid : 1 - b ^ 2 = (1 - b) * (1 + b) := by ring
    have hplus : ‖1 + b‖ ≤ 2 := by
      have h := norm_add_le (1 : Space) b
      rw [norm_one] at h
      linarith
    rw [hid]
    exact (norm_mul_le _ _).trans (by nlinarith only [mul_le_mul hb1 hplus (norm_nonneg _) (by positivity : 0 ≤ 2 * p)])
  have hid : binomial (n - 2) p - binomial n p = binomial (n - 2) p * (1 - b ^ 2) := by
    have hidx : n = n - 2 + 2 := by omega
    simp only [binomial, map_pow]
    change b ^ (n - 2) - b ^ n = b ^ (n - 2) * (1 - b ^ 2)
    conv_lhs => arg 2; rw [hidx, pow_add]
    ring
  rw [hid]
  exact (norm_mul_le _ _).trans
    (by simpa only [one_mul] using (mul_le_mul (norm_binomial_le_one (n - 2) hp hp₁) hb2
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))

theorem two_deleted_error {n : ℕ} (hn : 2 ≤ n) {p A : ℝ} (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (hmean : (n : ℝ) * p ≤ A) :
    ‖binomial (n - 2) p - poisson ((n : ℝ) * p)‖ ≤
      4 * (p + (n : ℝ) * p ^ 2) * Real.exp (2 * A + 2) := by
  have hA : 0 ≤ A := (mul_nonneg (Nat.cast_nonneg n) hp).trans hmean
  have he : 1 ≤ Real.exp (2 * A + 2) := Real.one_le_exp (by linarith)
  have htriangle : ‖binomial (n - 2) p - poisson ((n : ℝ) * p)‖ ≤
      ‖binomial (n - 2) p - binomial n p‖ + ‖binomial n p - poisson ((n : ℝ) * p)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le
      (binomial (n - 2) p - binomial n p) (binomial n p - poisson ((n : ℝ) * p))
  have h := htriangle.trans (add_le_add (delete_two_error hn hp hp₁) (first_order_error n hp hp₁ hmean))
  have hscale := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4 * p)
  nlinarith only [h, hscale]

end PaperP1.CompletedBinomial
