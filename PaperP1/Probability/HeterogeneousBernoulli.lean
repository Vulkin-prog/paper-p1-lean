module

public import PaperP1.Analysis.FiniteExponentialProducts
public import PaperP1.Probability.FinitePoissonCharlierConversion

/-! # Exact heterogeneous Bernoulli products and their analytic Poisson correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeterogeneousBernoulli

open Finset PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.CompletedBinomial PaperP1.FiniteExponentialProducts

variable {ι : Type*}

def base (G : Finset ι) (p : ι → ℝ) : Space := ofFinite (∏ i ∈ G, bernoulli (p i))

def mean (G : Finset ι) (p : ι → ℝ) : ℝ := ∑ i ∈ G, p i

def powerSum (G : Finset ι) (p : ι → ℝ) (r : ℕ) : ℝ := ∑ i ∈ G, (p i) ^ r

theorem mean_nonneg (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i) : 0 ≤ mean G p :=
  sum_nonneg hp

theorem powerSum_nonneg (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i) (r : ℕ) :
    0 ≤ powerSum G p r := sum_nonneg (fun i hi ↦ pow_nonneg (hp i hi) r)

theorem base_eq_product (G : Finset ι) (p : ι → ℝ) :
    base G p = product G (fun i ↦ p i • delta) := by
  rw [base, map_prod]
  exact prod_congr rfl (fun i _ ↦ bernoulli_eq (p i))

theorem exponentialProduct_eq_poisson (G : Finset ι) (p : ι → ℝ) :
    exponentialProduct G (fun i ↦ p i • delta) = poisson (mean G p) := by
  rw [exponentialProduct, ← NormedSpace.exp_sum, poisson, mean, sum_smul]

theorem quadraticCorrection_eq (G : Finset ι) (p : ι → ℝ) :
    quadraticCorrection G (fun i ↦ p i • delta) = (powerSum G p 2 / 2) • delta ^ 2 := by
  simp only [quadraticCorrection, smul_pow, smul_smul]
  rw [← sum_smul]
  congr 1
  rw [powerSum, sum_div]
  exact sum_congr rfl (fun _ _ ↦ by ring)

theorem norm_power_sum_le (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i) (r : ℕ) :
    (∑ i ∈ G, ‖p i • delta‖ ^ r) ≤ (2 : ℝ) ^ r * powerSum G p r := by
  calc
    _ ≤ ∑ i ∈ G, (2 * p i) ^ r := sum_le_sum (fun i hi ↦
      pow_le_pow_left₀ (norm_nonneg _) (norm_parameter_le (hp i hi)) r)
    _ = _ := by simp only [mul_pow, mul_sum, powerSum]

theorem norm_base_le_one (G : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1) : ‖base G p‖ ≤ 1 := by
  rw [base, map_prod]
  apply (Finset.norm_prod_le _ _).trans_eq
  apply prod_eq_one
  intro i hi
  rw [norm_ofFinite]
  exact l1Norm_probability (bernoulli_isProbability (hp i hi).1 (hp i hi).2)

theorem first_order_error (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i)
    {M : ℝ} (hmean : mean G p ≤ M) :
    ‖base G p - poisson (mean G p)‖ ≤ 4 * powerSum G p 2 * Real.exp (2 * M) := by
  have h := norm_first_order_le G (fun i ↦ p i • delta)
  have hpos := powerSum_nonneg G p hp 2
  rw [← base_eq_product, exponentialProduct_eq_poisson] at h
  have h₂ : (∑ i ∈ G, ‖p i • delta‖ ^ 2) ≤ 4 * powerSum G p 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using norm_power_sum_le G p hp 2
  have h₁ : (∑ i ∈ G, ‖p i • delta‖) ≤ 2 * M := by
    have hsum := norm_power_sum_le G p hp 1
    simp only [pow_one, powerSum] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left hmean (by norm_num))
  exact h.trans (mul_le_mul h₂ (Real.exp_le_exp.mpr h₁) (Real.exp_pos _).le
    (by positivity : 0 ≤ 4 * powerSum G p 2))

theorem quadratic_error (G : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ G, 0 ≤ p i)
    {M : ℝ} (hmean : mean G p ≤ M) :
    ‖base G p - quadratic (mean G p) (-powerSum G p 2)‖ ≤
      16 * Real.exp (2 * M) * (powerSum G p 3 + (powerSum G p 2) ^ 2) := by
  have h := norm_quadratic_error_le G (fun i ↦ p i • delta)
  have hpos₂ := powerSum_nonneg G p hp 2
  have hpos₃ := powerSum_nonneg G p hp 3
  rw [← base_eq_product, exponentialProduct_eq_poisson, quadraticCorrection_eq] at h
  have hid : base G p - quadratic (mean G p) (-powerSum G p 2) =
      base G p - poisson (mean G p) + (powerSum G p 2 / 2) • (delta ^ 2 * poisson (mean G p)) := by
    simp only [quadratic, neg_div, neg_smul]
    module
  rw [smul_mul_assoc] at h
  rw [hid]
  have h₂ := norm_power_sum_le G p hp 2
  have h₃ := norm_power_sum_le G p hp 3
  have h₁ : (∑ i ∈ G, ‖p i • delta‖) ≤ 2 * M := by
    have hsum := norm_power_sum_le G p hp 1
    simp only [pow_one, powerSum] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left hmean (by norm_num))
  calc
    _ ≤ (2 * (∑ i ∈ G, ‖p i • delta‖ ^ 3) + (∑ i ∈ G, ‖p i • delta‖ ^ 2) ^ 2) *
        Real.exp (∑ i ∈ G, ‖p i • delta‖) := h
    _ ≤ (2 * ((2 : ℝ) ^ 3 * powerSum G p 3) + ((2 : ℝ) ^ 2 * powerSum G p 2) ^ 2) *
        Real.exp (2 * M) := by gcongr
    _ = _ := by ring

end PaperP1.HeterogeneousBernoulli
