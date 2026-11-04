module

public import PaperP1.Probability.PositionalPoissonObservables
public import Mathlib.Data.Nat.Factorial.Cast

/-! # Actual coordinate moments and accidental pairs in the independent Poisson field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonPairs

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPoissonObservables

variable {ι : Type*}

local instance poissonPairsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem hasSum_coordinate_mean (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (x : ι) (hx : x ∈ G) :
    HasSum (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) * (v x : ℝ))
      (p x) := by
  simpa only [subsetCount_eq_sum, sum_singleton, Nat.descFactorial_one, pow_one] using
    hasSum_subset_factorial G {x} (singleton_subset_iff.mpr hx) p hp 1

theorem hasSum_coordinate_factorial_two (G : Finset ι) (p : ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x) (x : ι) (hx : x ∈ G) :
    HasSum (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
      ((v x : ℝ) * ((v x : ℝ) - 1))) ((p x) ^ 2) := by
  simpa only [subsetCount_eq_sum, sum_singleton, Nat.cast_descFactorial_two] using
    hasSum_subset_factorial G {x} (singleton_subset_iff.mpr hx) p hp 2

theorem hasSum_pair_product (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (x y : ι) (hx : x ∈ G) (hy : y ∈ G) (hxy : x ≠ y) :
    HasSum (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
      ((v x : ℝ) * (v y : ℝ))) (p x * p y) := by
  have hs := hasSum_subset_factorial G {x, y}
    (insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩) p hp 2
  simp only [subsetCount_eq_sum, sum_pair hxy, Nat.cast_descFactorial_two, Nat.cast_add] at hs
  have h := ((hs.sub (hasSum_coordinate_factorial_two G p hp x hx)).sub
    (hasSum_coordinate_factorial_two G p hp y hy)).mul_left (1 / 2 : ℝ)
  convert h using 1
  · funext v
    ring
  · ring

theorem occupied_pair_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (x y : ι) (hx : x ∈ G) (hy : y ∈ G) (hxy : x ≠ y) :
    Summable (fun v : Configuration ι ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
      (if 0 < v x ∧ 0 < v y then 1 else 0)) ∧
      (∑' v : Configuration ι, coeff v (PositionalBernoulliProducts.poisson G p) *
        (if 0 < v x ∧ 0 < v y then 1 else 0)) ≤ p x * p y := by
  have hmoment := hasSum_pair_product G p hp x y hx hy hxy
  have hnonneg := (poisson_isProbability G p hp).1
  have hpoint (v : Configuration ι) :
      coeff v (PositionalBernoulliProducts.poisson G p) * (if 0 < v x ∧ 0 < v y then 1 else 0) ≤
        coeff v (PositionalBernoulliProducts.poisson G p) * ((v x : ℝ) * (v y : ℝ)) := by
    apply mul_le_mul_of_nonneg_left ?_ (hnonneg v)
    split_ifs with hv
    · have hx1 : (1 : ℝ) ≤ v x := by exact_mod_cast Nat.succ_le_of_lt hv.1
      have hy1 : (1 : ℝ) ≤ v y := by exact_mod_cast Nat.succ_le_of_lt hv.2
      have hh := mul_le_mul hx1 hy1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ v x)
      simpa only [one_mul] using hh
    · positivity
  have hs := Summable.of_nonneg_of_le (fun v ↦
    mul_nonneg (hnonneg v) (by split_ifs <;> norm_num)) hpoint hmoment.summable
  exact ⟨hs, (hs.tsum_le_tsum hpoint hmoment.summable).trans_eq hmoment.tsum_eq⟩

end PaperP1.PositionalPoissonPairs
