module

public import PaperP1.Probability.PolynomialWeightTransfer

/-! # Joint control of finitely many nonnegative moment tests

Summing the tests before integration avoids a factor equal to the number of
coordinates. All expectations and changes of summation order are absolute.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteMomentComparison

open Finset

variable {α κ : Type*}

theorem summable_test (a w f : α → ℝ) (ha : ∀ v, 0 ≤ a v)
    (hf : ∀ v, 0 ≤ f v) (hfw : ∀ v, f v ≤ w v)
    (hs : Summable (fun v ↦ a v * w v)) : Summable (fun v ↦ a v * f v) :=
  Summable.of_nonneg_of_le (fun v ↦ mul_nonneg (ha v) (hf v))
    (fun v ↦ mul_le_mul_of_nonneg_left (hfw v) (ha v)) hs

theorem finite_tests_bound (S : Finset κ) (a b w : α → ℝ) (f : κ → α → ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v)
    (hf : ∀ i ∈ S, ∀ v, 0 ≤ f i v)
    (hfw : ∀ v, (∑ i ∈ S, f i v) ≤ w v)
    (hsa : Summable (fun v ↦ a v * w v))
    (hsb : Summable (fun v ↦ b v * w v))
    (hsd : Summable (fun v ↦ |a v - b v| * w v)) :
    (∑ i ∈ S, |(∑' v, a v * f i v) - ∑' v, b v * f i v|) ≤
      ∑' v, |a v - b v| * w v := by
  have hle (i : κ) (hi : i ∈ S) (v : α) : f i v ≤ w v :=
    (single_le_sum (fun k hk ↦ hf k hk v) hi).trans (hfw v)
  have hAs (i : κ) (hi : i ∈ S) := summable_test a w (f i) ha (hf i hi) (hle i hi) hsa
  have hBs (i : κ) (hi : i ∈ S) := summable_test b w (f i) hb (hf i hi) (hle i hi) hsb
  have hDs (i : κ) (hi : i ∈ S) := summable_test (fun v ↦ |a v - b v|) w (f i)
    (fun _ ↦ abs_nonneg _) (hf i hi) (hle i hi) hsd
  have hpoint (i : κ) (hi : i ∈ S) :
      |(∑' v, a v * f i v) - ∑' v, b v * f i v| ≤ ∑' v, |a v - b v| * f i v := by
    rw [← (hAs i hi).tsum_sub (hBs i hi)]
    have hh := norm_tsum_le_tsum_norm ((hAs i hi).sub (hBs i hi)).norm
    simpa only [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_of_nonneg (hf i hi _)] using hh
  calc
    _ ≤ ∑ i ∈ S, ∑' v, |a v - b v| * f i v := sum_le_sum hpoint
    _ = ∑' v, ∑ i ∈ S, |a v - b v| * f i v := (Summable.tsum_finsetSum hDs).symm
    _ ≤ _ := (summable_sum hDs).tsum_le_tsum
      (fun v ↦ by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hfw v) (abs_nonneg _)) hsd

end PaperP1.FiniteMomentComparison
