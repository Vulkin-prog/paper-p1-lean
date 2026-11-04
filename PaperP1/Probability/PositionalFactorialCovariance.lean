module

public import PaperP1.Probability.FiniteMomentComparison
public import PaperP1.Probability.PositionalPoissonPairs

/-! # Factorial covariance matrices of full counting fields -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalFactorialCovariance

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalCountProjection

variable {ι : Type*}

local instance covarianceDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def mean (ν : Space ι) (x : ι) : ℝ := ∑' v, coeff v ν * (v x : ℝ)

def factorialTest (x y : ι) (v : Configuration ι) : ℝ :=
  (v x : ℝ) * (v y : ℝ) - if x = y then (v x : ℝ) else 0

def second (ν : Space ι) (x y : ι) : ℝ := ∑' v, coeff v ν * factorialTest x y v

def covariance (ν : Space ι) (x y : ι) : ℝ := second ν x y - mean ν x * mean ν y

def weight (v : Configuration ι) : ℝ := (1 + (totalCount v : ℝ)) ^ 2

theorem finite_count_le (G : Finset ι) (v : Configuration ι) :
    (∑ x ∈ G, (v x : ℝ)) ≤ (totalCount v : ℝ) := by
  have he : (∑ x ∈ G, v x) = ∑ x ∈ v.support.filter (fun x ↦ x ∈ G), v x := by
    symm
    apply sum_subset (fun x hx ↦ (mem_filter.mp hx).2)
    intro x _hx hx
    exact Finsupp.notMem_support_iff.mp (fun hv ↦ hx (mem_filter.mpr ⟨hv, _hx⟩))
  have hh : (∑ x ∈ G, v x) ≤ ∑ x ∈ v.support, v x := by
    rw [he]
    exact sum_le_sum_of_subset (filter_subset _ _)
  have ht : totalCount v = ∑ x ∈ v.support, v x := by
    simp [totalCount, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [← ht] at hh
  exact_mod_cast hh

theorem factorialTest_nonneg (x y : ι) (v : Configuration ι) : 0 ≤ factorialTest x y v := by
  by_cases hxy : x = y
  · subst y
    by_cases hv : v x = 0
    · simp [factorialTest, hv]
    · have hx : (1 : ℝ) ≤ v x := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv
      simp only [factorialTest, ite_true]
      nlinarith
  · simp only [factorialTest, ite_eq_right hxy, sub_zero]
    positivity

theorem factorialTest_le (x y : ι) (v : Configuration ι) :
    factorialTest x y v ≤ (v x : ℝ) * (v y : ℝ) := by
  unfold factorialTest
  apply sub_le_self
  split_ifs <;> positivity

theorem finite_first_test_bound (G : Finset ι) (v : Configuration ι) :
    (∑ x ∈ G, (v x : ℝ)) ≤ weight v := by
  have hh := finite_count_le G v
  have ht : (0 : ℝ) ≤ totalCount v := by positivity
  dsimp only [weight]
  nlinarith

theorem finite_second_test_bound (G : Finset ι) (v : Configuration ι) :
    (∑ z ∈ G ×ˢ G, factorialTest z.1 z.2 v) ≤ weight v := by
  calc
    _ ≤ ∑ z ∈ G ×ˢ G, (v z.1 : ℝ) * (v z.2 : ℝ) :=
      sum_le_sum (fun z _hz ↦ factorialTest_le z.1 z.2 v)
    _ = (∑ x ∈ G, (v x : ℝ)) ^ 2 := by
      rw [sum_product]
      change (∑ x ∈ G, ∑ y ∈ G, (v x : ℝ) * (v y : ℝ)) = _
      rw [← sum_mul_sum]
      ring
    _ ≤ (totalCount v : ℝ) ^ 2 := pow_le_pow_left₀ (sum_nonneg (fun _ _ ↦ by positivity))
      (finite_count_le G v) 2
    _ ≤ weight v := by
      dsimp only [weight]
      have ht : (0 : ℝ) ≤ totalCount v := by positivity
      nlinarith

theorem poisson_mean (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (x : ι) (hx : x ∈ G) : mean (PositionalBernoulliProducts.poisson G p) x = p x :=
  (PositionalPoissonPairs.hasSum_coordinate_mean G p hp x hx).tsum_eq

theorem poisson_second (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (x y : ι) (hx : x ∈ G) (hy : y ∈ G) :
    second (PositionalBernoulliProducts.poisson G p) x y = p x * p y := by
  by_cases hxy : x = y
  · subst y
    have hh := (PositionalPoissonPairs.hasSum_coordinate_factorial_two G p hp x hx).tsum_eq
    convert hh using 1
    · apply tsum_congr
      intro v
      simp only [factorialTest, ite_true]
      ring
    · ring
  · simpa only [second, factorialTest, ite_eq_right hxy, sub_zero] using
      (PositionalPoissonPairs.hasSum_pair_product G p hp x y hx hy hxy).tsum_eq

theorem poisson_covariance (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (x y : ι) (hx : x ∈ G) (hy : y ∈ G) :
    covariance (PositionalBernoulliProducts.poisson G p) x y = 0 := by
  rw [covariance, poisson_second G p hp x y hx hy, poisson_mean G p hp x hx,
    poisson_mean G p hp y hy, sub_self]

end PaperP1.PositionalFactorialCovariance
