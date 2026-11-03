module

public import PaperP1.Probability.PositionalCompoundPoisson
public import PaperP1.Analysis.FiniteExponentialProducts
public import Mathlib.Tactic.Module

/-! # Heterogeneous Bernoulli products retaining their original sites -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalBernoulliProducts

open Finset PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw
  PaperP1.CompletedPositionalLaw PaperP1.FiniteExponentialProducts

variable {ι : Type*}

local instance positionalBernoulliDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def site (x : ι) (p : ℝ) : Space ι := 1 + p • ofFinite (delta x)

def base (G : Finset ι) (p : ι → ℝ) : Space ι := ∏ x ∈ G, site x (p x)

def poisson (G : Finset ι) (p : ι → ℝ) : Space ι :=
  NormedSpace.exp (∑ x ∈ G, p x • ofFinite (delta x))

theorem site_norm_le_one (x : ι) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : ‖site x p‖ ≤ 1 := by
  have he : site x p = (1 - p) • (1 : Space ι) + p • ofFinite (atom (direction x)) := by
    simp only [site, delta, map_sub, map_one, smul_sub]
    module
  rw [he]
  have hh := norm_add_le ((1 - p) • (1 : Space ι)) (p • ofFinite (atom (direction x)))
  rw [norm_smul, norm_smul, norm_one, norm_ofFinite, l1Norm_atom, mul_one, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1), abs_of_nonneg hp] at hh
  linarith only [hh]

theorem norm_base_le_one (G : Finset ι) (p : ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x ∧ p x ≤ 1) : ‖base G p‖ ≤ 1 := by
  calc
    _ ≤ ∏ x ∈ G, ‖site x (p x)‖ := norm_prod_le _ _
    _ ≤ ∏ _x ∈ G, (1 : ℝ) := prod_le_prod₀ (fun x _ ↦ norm_nonneg (site x (p x)))
      (fun x hx ↦ site_norm_le_one x (p x) (hp x hx).1 (hp x hx).2)
    _ = 1 := by simp

theorem norm_parameter_le (x : ι) (p : ℝ) (hp : 0 ≤ p) :
    ‖p • ofFinite (delta x)‖ ≤ 2 * p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
  exact (mul_le_mul_of_nonneg_left (norm_delta_le x) hp).trans_eq (mul_comm _ _)

theorem norm_one_sub_site (x : ι) (p : ℝ) (hp : 0 ≤ p) : ‖1 - site x p‖ ≤ 2 * p := by
  rw [site, show (1 : Space ι) - (1 + p • ofFinite (delta x)) = -(p • ofFinite (delta x)) by abel, norm_neg]
  exact norm_parameter_le x p hp

theorem norm_poisson_le_one (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x) :
    ‖poisson G p‖ ≤ 1 := by
  have he : poisson G p = ∏ x ∈ G, PositionalPoissonJump.jump (direction x) (p x) := by
    rw [poisson, NormedSpace.exp_sum]
    apply prod_congr rfl
    intro x _
    rw [PositionalPoissonJump.jump, delta, map_sub, map_one]
  rw [he]
  exact (PositivePositionalConvolution.norm_isProbability
    (PositivePositionalConvolution.prod_isProbability G _
      (fun x hx ↦ PositivePositionalConvolution.jump_isProbability _ _ (hp x hx)))).le

theorem first_order_error (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (M : ℝ) (hmean : ∑ x ∈ G, p x ≤ M) :
    ‖base G p - poisson G p‖ ≤ 4 * (∑ x ∈ G, (p x) ^ 2) * Real.exp (2 * M) := by
  have hh := norm_first_order_le G (fun x ↦ p x • ofFinite (delta x))
  have hbase : product G (fun x ↦ p x • ofFinite (delta x)) = base G p := rfl
  have hpoisson : exponentialProduct G (fun x ↦ p x • ofFinite (delta x)) = poisson G p := by
    rw [exponentialProduct, poisson, NormedSpace.exp_sum]
  rw [hbase, hpoisson] at hh
  have hsq : (∑ x ∈ G, ‖p x • ofFinite (delta x)‖ ^ 2) ≤ 4 * ∑ x ∈ G, (p x) ^ 2 := by
    calc
      _ ≤ ∑ x ∈ G, (2 * p x) ^ 2 := sum_le_sum fun x hx ↦
        pow_le_pow_left₀ (norm_nonneg _) (norm_parameter_le x (p x) (hp x hx)) 2
      _ = _ := by simp only [mul_pow, mul_sum]; norm_num
  have hsum : (∑ x ∈ G, ‖p x • ofFinite (delta x)‖) ≤ 2 * M := by
    calc
      _ ≤ ∑ x ∈ G, 2 * p x := sum_le_sum fun x hx ↦ norm_parameter_le x (p x) (hp x hx)
      _ = 2 * ∑ x ∈ G, p x := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (by norm_num)
  exact hh.trans (mul_le_mul hsq (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _)
    (mul_nonneg (by norm_num) (sum_nonneg fun x _ ↦ sq_nonneg (p x))))

theorem base_factorization (G e : Finset ι) (p : ι → ℝ) (he : e ⊆ G) :
    base (G \ e) p * base e p = base G p := by
  classical
  exact prod_sdiff (f := fun x ↦ site x (p x)) he

end PaperP1.PositionalBernoulliProducts
