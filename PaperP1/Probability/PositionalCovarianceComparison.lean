module

public import PaperP1.Probability.PositionalFactorialCovariance

/-! # Dimension-independent control of the entire factorial covariance matrix -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCovarianceComparison

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalFactorialCovariance

variable {ι : Type*}

theorem tensor_bound (G : Finset ι) (a b : ι → ℝ)
    (ha : ∀ x ∈ G, 0 ≤ a x) (hb : ∀ x ∈ G, 0 ≤ b x) :
    (∑ z ∈ G ×ˢ G, |a z.1 * a z.2 - b z.1 * b z.2|) ≤
      ((∑ x ∈ G, a x) + ∑ x ∈ G, b x) * ∑ x ∈ G, |a x - b x| := by
  have hpoint (x y : ι) (hx : x ∈ G) (hy : y ∈ G) :
      |a x * a y - b x * b y| ≤ a x * |a y - b y| + |a x - b x| * b y := by
    calc
      _ = |a x * (a y - b y) + (a x - b x) * b y| := by congr 1; ring
      _ ≤ |a x * (a y - b y)| + |(a x - b x) * b y| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (ha x hx), abs_of_nonneg (hb y hy)]
  calc
    _ ≤ ∑ z ∈ G ×ˢ G, (a z.1 * |a z.2 - b z.2| + |a z.1 - b z.1| * b z.2) :=
      sum_le_sum (fun z hz ↦ hpoint z.1 z.2 (mem_product.mp hz).1 (mem_product.mp hz).2)
    _ = _ := by
      simp only [sum_product, sum_add_distrib, ← mul_sum, ← sum_mul]
      ring

theorem first_error_bound (G : Finset ι) (ν μ : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (hμ : ∀ v, 0 ≤ coeff v μ)
    (hsν : Summable (fun v ↦ coeff v ν * weight v))
    (hsμ : Summable (fun v ↦ coeff v μ * weight v))
    (hsd : Summable (fun v ↦ |coeff v ν - coeff v μ| * weight v)) :
    (∑ x ∈ G, |mean ν x - mean μ x|) ≤ ∑' v, |coeff v ν - coeff v μ| * weight v :=
  FiniteMomentComparison.finite_tests_bound G (fun v ↦ coeff v ν) (fun v ↦ coeff v μ)
    weight (fun x v ↦ (v x : ℝ)) hν hμ (fun _ _ _ ↦ by positivity)
    (finite_first_test_bound G) hsν hsμ hsd

theorem second_error_bound (G : Finset ι) (ν μ : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (hμ : ∀ v, 0 ≤ coeff v μ)
    (hsν : Summable (fun v ↦ coeff v ν * weight v))
    (hsμ : Summable (fun v ↦ coeff v μ * weight v))
    (hsd : Summable (fun v ↦ |coeff v ν - coeff v μ| * weight v)) :
    (∑ z ∈ G ×ˢ G, |second ν z.1 z.2 - second μ z.1 z.2|) ≤
      ∑' v, |coeff v ν - coeff v μ| * weight v :=
  FiniteMomentComparison.finite_tests_bound (G ×ˢ G) (fun v ↦ coeff v ν) (fun v ↦ coeff v μ)
    weight (fun z v ↦ factorialTest z.1 z.2 v) hν hμ
    (fun z _ v ↦ factorialTest_nonneg z.1 z.2 v) (finite_second_test_bound G) hsν hsμ hsd

theorem poisson_bound (G : Finset ι) (ν : Space ι) (p : ι → ℝ)
    (hν : ∀ v, 0 ≤ coeff v ν) (hp : ∀ x ∈ G, 0 ≤ p x)
    (hsν : Summable (fun v ↦ coeff v ν * weight v))
    (hsU : Summable (fun v ↦ coeff v (PositionalBernoulliProducts.poisson G p) * weight v))
    (hsd : Summable (fun v ↦ |coeff v ν - coeff v (PositionalBernoulliProducts.poisson G p)| * weight v)) :
    let D := ∑' v, |coeff v ν - coeff v (PositionalBernoulliProducts.poisson G p)| * weight v
    (∑ z ∈ G ×ˢ G, |covariance ν z.1 z.2|) ≤ (1 + 2 * (∑ x ∈ G, p x) + D) * D := by
  let U := PositionalBernoulliProducts.poisson G p
  let D := ∑' v, |coeff v ν - coeff v U| * weight v
  have hU := (PositionalPoissonObservables.poisson_isProbability G p hp).1
  have hD : 0 ≤ D := tsum_nonneg (fun v ↦ mul_nonneg (abs_nonneg _) (by dsimp [weight]; positivity))
  have h1 := first_error_bound G ν U hν hU hsν hsU hsd
  have h2 := second_error_bound G ν U hν hU hsν hsU hsd
  have hmeanν (x : ι) : 0 ≤ mean ν x := tsum_nonneg (fun v ↦ mul_nonneg (hν v) (by positivity))
  have hmeanU (x : ι) : 0 ≤ mean U x := tsum_nonneg (fun v ↦ mul_nonneg (hU v) (by positivity))
  have hsumU : (∑ x ∈ G, mean U x) = ∑ x ∈ G, p x :=
    sum_congr rfl (fun x hx ↦ poisson_mean G p hp x hx)
  have hsumν : (∑ x ∈ G, mean ν x) ≤ (∑ x ∈ G, p x) + D := by
    calc
      _ ≤ ∑ x ∈ G, (mean U x + |mean ν x - mean U x|) := sum_le_sum (fun x _hx ↦ by
        have hh := le_abs_self (mean ν x - mean U x)
        linarith)
      _ = (∑ x ∈ G, mean U x) + ∑ x ∈ G, |mean ν x - mean U x| := sum_add_distrib
      _ ≤ _ := by rw [hsumU]; exact add_le_add le_rfl h1
  have htensor := tensor_bound G (mean ν) (mean U) (fun x _hx ↦ hmeanν x) (fun x _hx ↦ hmeanU x)
  have htensor' : (∑ z ∈ G ×ˢ G, |mean ν z.1 * mean ν z.2 - mean U z.1 * mean U z.2|) ≤
      (2 * (∑ x ∈ G, p x) + D) * D := by
    apply htensor.trans
    apply mul_le_mul
    · rw [hsumU]
      linarith only [hsumν]
    · exact h1
    · exact sum_nonneg (fun _ _ ↦ abs_nonneg _)
    · exact add_nonneg (mul_nonneg (by norm_num) (sum_nonneg hp)) hD
  have hpoint (z : ι × ι) (hz : z ∈ G ×ˢ G) :
      |covariance ν z.1 z.2| ≤ |second ν z.1 z.2 - second U z.1 z.2| +
        |mean ν z.1 * mean ν z.2 - mean U z.1 * mean U z.2| := by
    have hzero := poisson_covariance G p hp z.1 z.2 (mem_product.mp hz).1 (mem_product.mp hz).2
    have he : covariance ν z.1 z.2 = (second ν z.1 z.2 - second U z.1 z.2) -
        (mean ν z.1 * mean ν z.2 - mean U z.1 * mean U z.2) := by
      dsimp only [covariance] at hzero ⊢
      dsimp only [U]
      linarith only [hzero]
    rw [he]
    have hh := abs_sub_le (second ν z.1 z.2 - second U z.1 z.2) 0
      (mean ν z.1 * mean ν z.2 - mean U z.1 * mean U z.2)
    simpa only [sub_zero, zero_sub, abs_neg] using hh
  calc
    _ ≤ ∑ z ∈ G ×ˢ G, (|second ν z.1 z.2 - second U z.1 z.2| +
        |mean ν z.1 * mean ν z.2 - mean U z.1 * mean U z.2|) := sum_le_sum hpoint
    _ = (∑ z ∈ G ×ˢ G, |second ν z.1 z.2 - second U z.1 z.2|) +
        ∑ z ∈ G ×ˢ G, |mean ν z.1 * mean ν z.2 - mean U z.1 * mean U z.2| := sum_add_distrib
    _ ≤ D + (2 * (∑ x ∈ G, p x) + D) * D := add_le_add h2 htensor'
    _ = _ := by ring

end PaperP1.PositionalCovarianceComparison
