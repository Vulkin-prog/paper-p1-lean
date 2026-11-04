module

public import PaperP1.Probability.PositionalFactorialCovariance
public import PaperP1.Probability.PositionalGroundSupport

/-! # Exact second factorial cumulants of the projected total count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCountCumulant

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalFactorialCovariance PaperP1.PositionalGroundSupport
  PaperP1.PositionalCountProjection

variable {ι : Type*}

def scalar (P : CompletedLaw.Space) : ℝ :=
  (∑' k : ℕ, CompletedLaw.coeff k P * ((k : ℝ) * ((k : ℝ) - 1))) -
    (∑' k : ℕ, CompletedLaw.coeff k P * (k : ℝ)) ^ 2

theorem onGround_count (G : Finset ι) (v : Configuration ι) (hv : OnGround G v) :
    (∑ x ∈ G, (v x : ℝ)) = (totalCount v : ℝ) := by
  classical
  have ht : totalCount v = ∑ x ∈ v.support, v x := by
    simp [totalCount, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [ht, Nat.cast_sum]
  symm
  apply sum_subset
  · intro x hx
    by_contra hxG
    exact Finsupp.mem_support_iff.mp hx (hv x hxG)
  · intro x _hx hx
    rw [Finsupp.notMem_support_iff.mp hx, Nat.cast_zero]

theorem finite_factorial_sum (G : Finset ι) (v : Configuration ι) :
    (∑ z ∈ G ×ˢ G, factorialTest z.1 z.2 v) =
      (∑ x ∈ G, (v x : ℝ)) * ((∑ x ∈ G, (v x : ℝ)) - 1) := by
  classical
  rw [sum_product]
  change (∑ x ∈ G, ∑ y ∈ G, ((v x : ℝ) * (v y : ℝ) - if x = y then (v x : ℝ) else 0)) = _
  simp_rw [sum_sub_distrib]
  rw [← sum_mul_sum]
  have hd : (∑ x ∈ G, ∑ y ∈ G, if x = y then (v x : ℝ) else 0) = ∑ x ∈ G, (v x : ℝ) := by
    apply sum_congr rfl
    intro x hx
    simp [hx]
  rw [hd]
  ring

theorem coordinate_summable (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν)
    (hs : Summable (fun v ↦ coeff v ν * weight v)) (x : ι) :
    Summable (fun v ↦ coeff v ν * (v x : ℝ)) :=
  FiniteMomentComparison.summable_test _ _ _ hν (fun _ ↦ by positivity)
    (fun v ↦ by simpa only [sum_singleton] using finite_first_test_bound {x} v) hs

theorem factorial_summable (G : Finset ι) (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν)
    (hs : Summable (fun v ↦ coeff v ν * weight v)) (z : ι × ι) (hz : z ∈ G ×ˢ G) :
    Summable (fun v ↦ coeff v ν * factorialTest z.1 z.2 v) :=
  FiniteMomentComparison.summable_test _ _ _ hν (factorialTest_nonneg z.1 z.2)
    (fun v ↦ (single_le_sum (fun z _hz ↦ factorialTest_nonneg z.1 z.2 v) hz).trans
      (finite_second_test_bound G v)) hs

theorem sum_mean (G : Finset ι) (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν)
    (hground : Supported G ν) (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    (∑ x ∈ G, mean ν x) = ∑' v, coeff v ν * (totalCount v : ℝ) := by
  calc
    _ = ∑' v, ∑ x ∈ G, coeff v ν * (v x : ℝ) :=
      (Summable.tsum_finsetSum (fun x _hx ↦ coordinate_summable ν hν hs x)).symm
    _ = _ := by
      apply tsum_congr
      intro v
      rw [← mul_sum]
      by_cases hv : OnGround G v
      · rw [onGround_count G v hv]
      · rw [hground v hv, zero_mul, zero_mul]

theorem sum_second (G : Finset ι) (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν)
    (hground : Supported G ν) (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    (∑ z ∈ G ×ˢ G, second ν z.1 z.2) =
      ∑' v, coeff v ν * ((totalCount v : ℝ) * ((totalCount v : ℝ) - 1)) := by
  calc
    _ = ∑' v, ∑ z ∈ G ×ˢ G, coeff v ν * factorialTest z.1 z.2 v :=
      (Summable.tsum_finsetSum (factorial_summable G ν hν hs)).symm
    _ = _ := by
      apply tsum_congr
      intro v
      rw [← mul_sum, finite_factorial_sum]
      by_cases hv : OnGround G v
      · rw [onGround_count G v hv]
      · rw [hground v hv, zero_mul, zero_mul]

theorem nat_second_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  by_cases hz : n = 0
  · simp [hz]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    positivity

theorem nat_second_le (n : ℕ) : (n : ℝ) * ((n : ℝ) - 1) ≤ (1 + (n : ℝ)) ^ 2 := by
  have ht : (0 : ℝ) ≤ n := by positivity
  nlinarith

theorem projection_test_eq (ν : Space ι) (f : ℕ → ℝ)
    (hs : Summable (fun v ↦ coeff v ν * f (totalCount v))) :
    (∑' k, CompletedLaw.coeff k (projection ν) * f k) = ∑' v, coeff v ν * f (totalCount v) := by
  simp only [projection_coeff]
  exact PushforwardMass.test_map _ _ _ hs

theorem scalar_eq_field (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν)
    (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    scalar (projection ν) =
      (∑' v, coeff v ν * ((totalCount v : ℝ) * ((totalCount v : ℝ) - 1))) -
        (∑' v, coeff v ν * (totalCount v : ℝ)) ^ 2 := by
  have hfirst : Summable (fun v ↦ coeff v ν * (totalCount v : ℝ)) :=
    FiniteMomentComparison.summable_test _ _ _ hν (fun _ ↦ by positivity) (fun v ↦ by
      dsimp only [weight]
      have ht : (0 : ℝ) ≤ totalCount v := by positivity
      nlinarith) hs
  have hsecond : Summable (fun v ↦ coeff v ν * ((totalCount v : ℝ) * ((totalCount v : ℝ) - 1))) :=
    FiniteMomentComparison.summable_test _ _ _ hν (fun v ↦ nat_second_nonneg (totalCount v))
      (fun v ↦ nat_second_le (totalCount v)) hs
  rw [scalar, projection_test_eq ν (fun k ↦ (k : ℝ) * ((k : ℝ) - 1)) hsecond,
    projection_test_eq ν (fun k ↦ (k : ℝ)) hfirst]

theorem scalar_eq_covariance_sum (G : Finset ι) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (hground : Supported G ν)
    (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    scalar (projection ν) = ∑ z ∈ G ×ˢ G, covariance ν z.1 z.2 := by
  rw [scalar_eq_field ν hν hs, ← sum_second G ν hν hground hs, ← sum_mean G ν hν hground hs]
  simp only [covariance, sum_sub_distrib]
  congr 1
  rw [sum_product]
  change (∑ x ∈ G, mean ν x) ^ 2 = ∑ x ∈ G, ∑ y ∈ G, mean ν x * mean ν y
  rw [← sum_mul_sum]
  ring

theorem abs_scalar_le (G : Finset ι) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (hground : Supported G ν)
    (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    |scalar (projection ν)| ≤ ∑ z ∈ G ×ˢ G, |covariance ν z.1 z.2| := by
  rw [scalar_eq_covariance_sum G ν hν hground hs]
  exact abs_sum_le_sum_abs _ _

end PaperP1.PositionalCountCumulant
