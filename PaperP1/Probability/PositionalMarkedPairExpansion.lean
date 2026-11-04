module

public import PaperP1.Probability.PositionalPoissonObservables
public import PaperP1.Probability.PositionalPairDeletion
public import PaperP1.Probability.PositionalCompoundPoisson
public import PaperP1.Analysis.BanachExponentialRemainder

/-! # Zero/one marked-pair expansion of the actual compound field

The quadratic remainder is bounded in the ordinary full-field norm. No
independent sample representation is assumed as an additional hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalMarkedPairExpansion

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositivePositionalConvolution
  PaperP1.PositionalPairDeletion PaperP1.PositionalCompoundPoisson

variable {ι : Type*}

def background (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ) : Space ι :=
  PositionalBernoulliProducts.poisson G (fun x ↦ p x - incidence E q x)

def generator (E : Finset (Finset ι)) (q : Finset ι → ℝ) : Space ι :=
  ∑ e ∈ E, q e • (ofFinite (atom (edgeVector e)) - 1)

def firstOrder (U : Space ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ) : Space ι :=
  (1 - ∑ e ∈ E, q e) • U + ∑ e ∈ E, q e • (ofFinite (atom (edgeVector e)) * U)

theorem factorization (G : Finset ι) (E : Finset (Finset ι)) (p : ι → ℝ) (q : Finset ι → ℝ) :
    target G E p q = background G E p q * NormedSpace.exp (generator E q) := by
  rw [target, background, PositionalPoissonObservables.poisson_product]
  congr 1
  simp only [PositionalPoissonJump.jump]
  rw [← NormedSpace.exp_sum]
  rfl

theorem norm_generator_le (E : Finset (Finset ι)) (q : Finset ι → ℝ)
    (hq : ∀ e ∈ E, 0 ≤ q e) : ‖generator E q‖ ≤ 2 * ∑ e ∈ E, q e := by
  calc
    _ ≤ ∑ e ∈ E, ‖q e • (ofFinite (atom (edgeVector e)) - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ E, 2 * q e := by
      apply sum_le_sum
      intro e he
      have hd : ‖ofFinite (atom (edgeVector e)) - 1‖ ≤ 2 := by
        simpa only [norm_ofFinite, l1Norm_atom, norm_one, one_add_one_eq_two] using
          norm_sub_le (ofFinite (atom (edgeVector e))) (1 : Space ι)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq e he)]
      nlinarith only [mul_le_mul_of_nonneg_left hd (hq e he)]
    _ = _ := (mul_sum _ _ _).symm

theorem firstOrder_factorization (U : Space ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ) :
    firstOrder U E q = U * (1 + generator E q) := by
  have he (e : Finset ι) : U * (q e • (ofFinite (atom (edgeVector e)) - 1)) =
      q e • (ofFinite (atom (edgeVector e)) * U) - q e • U := by
    rw [mul_smul_comm, mul_sub, mul_one, mul_comm U, smul_sub]
  rw [firstOrder, mul_add, mul_one, generator, mul_sum]
  simp_rw [he]
  rw [sum_sub_distrib, ← sum_smul]
  module

theorem first_order_error (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x - incidence E q x) (hq : ∀ e ∈ E, 0 ≤ q e) :
    ‖target G E p q - firstOrder (background G E p q) E q‖ ≤
      4 * (∑ e ∈ E, q e) ^ 2 * Real.exp (2 * ∑ e ∈ E, q e) := by
  have hU : ‖background G E p q‖ = 1 := norm_isProbability
    (PositionalPoissonObservables.poisson_isProbability G _ hp)
  have hv := norm_generator_le E q hq
  rw [factorization, firstOrder_factorization, ← mul_sub]
  calc
    _ ≤ ‖background G E p q‖ * ‖NormedSpace.exp (generator E q) - (1 + generator E q)‖ := norm_mul_le _ _
    _ = ‖NormedSpace.exp (generator E q) - (1 + generator E q)‖ := by rw [hU, one_mul]
    _ ≤ ‖generator E q‖ ^ 2 * Real.exp ‖generator E q‖ :=
      BanachExponentialRemainder.norm_exp_sub_linear_le _
    _ ≤ (2 * ∑ e ∈ E, q e) ^ 2 * Real.exp (2 * ∑ e ∈ E, q e) := by gcongr
    _ = _ := by ring

theorem image_firstOrder_bound (U : Space ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ)
    (hq : ∀ e ∈ E, 0 ≤ q e) (K : Space ι →L[ℝ] Space ι) :
    ‖K (firstOrder U E q) - U‖ ≤
      |1 - ∑ e ∈ E, q e| * ‖K U - U‖ +
        ∑ e ∈ E, q e * ‖K (ofFinite (atom (edgeVector e)) * U) - U‖ := by
  have he : K (firstOrder U E q) - U =
      (1 - ∑ e ∈ E, q e) • (K U - U) +
        ∑ e ∈ E, q e • (K (ofFinite (atom (edgeVector e)) * U) - U) := by
    simp only [firstOrder, map_add, map_smul, map_sum, smul_sub, sum_sub_distrib]
    rw [← sum_smul]
    module
  rw [he]
  calc
    _ ≤ ‖(1 - ∑ e ∈ E, q e) • (K U - U)‖ +
        ‖∑ e ∈ E, q e • (K (ofFinite (atom (edgeVector e)) * U) - U)‖ := norm_add_le _ _
    _ ≤ ‖(1 - ∑ e ∈ E, q e) • (K U - U)‖ +
        ∑ e ∈ E, ‖q e • (K (ofFinite (atom (edgeVector e)) * U) - U)‖ :=
      add_le_add le_rfl (norm_sum_le _ _)
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs]
      congr 1
      exact sum_congr rfl (fun e he ↦ by rw [abs_of_nonneg (hq e he)])

theorem approximation_bound (G : Finset ι) (E : Finset (Finset ι))
    (p : ι → ℝ) (q : Finset ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x - incidence E q x) (hq : ∀ e ∈ E, 0 ≤ q e)
    (K : Space ι →L[ℝ] Space ι) (hK : ∀ ν, ‖K ν‖ ≤ ‖ν‖) :
    let U := background G E p q
    ‖K (target G E p q) - U‖ ≤
      4 * (∑ e ∈ E, q e) ^ 2 * Real.exp (2 * ∑ e ∈ E, q e) +
      |1 - ∑ e ∈ E, q e| * ‖K U - U‖ +
        ∑ e ∈ E, q e * ‖K (ofFinite (atom (edgeVector e)) * U) - U‖ := by
  let U := background G E p q
  let R := firstOrder U E q
  have hfirst : ‖K (target G E p q) - K R‖ ≤
      4 * (∑ e ∈ E, q e) ^ 2 * Real.exp (2 * ∑ e ∈ E, q e) := by
    rw [← map_sub]
    exact (hK _).trans (first_order_error G E p q hp hq)
  have hlinear := image_firstOrder_bound U E q hq K
  have htri := norm_add_le (K (target G E p q) - K R) (K R - U)
  rw [sub_add_sub_cancel] at htri
  dsimp only
  linarith only [hfirst, hlinear, htri]

end PaperP1.PositionalMarkedPairExpansion
