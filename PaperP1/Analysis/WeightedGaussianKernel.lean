module

public import PaperP1.Analysis.GaussianExponentialSums

/-! # Actual weighted symmetric kernels and Gaussian polynomial means -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedGaussianKernel
open Finset Nat MeasureTheory PaperP1
open scoped Classical ComplexConjugate

open GaussianExponentialSums

theorem weighted_symmetric_bound {ι : Type*} (S : Finset ι) (m x : ι → ℝ)
    (k : ι → ι → ℝ) (L : ℝ) (hm : ∀ i ∈ S, 0 ≤ m i)
    (hk : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ k i j)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, k i j=k j i)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, m j*k i j) ≤ L) :
    (∑ i ∈ S, ∑ j ∈ S, m i*m j*k i j*x i*x j) ≤
      L*∑ i ∈ S, m i*x i^2 := by
  have hrows : (∑ i ∈ S, ∑ j ∈ S, m i*m j*k i j*x i^2) ≤
      L*∑ i ∈ S, m i*x i^2 := by
    calc
      _ = ∑ i ∈ S, (∑ j ∈ S, m j*k i j)*(m i*x i^2) := by
        apply sum_congr rfl
        intro i hi
        rw [sum_mul]
        apply sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i ∈ S, L*(m i*x i^2) := sum_le_sum (fun i hi ↦
        mul_le_mul_of_nonneg_right (hrow i hi) (mul_nonneg (hm i hi) (sq_nonneg _)))
      _ = _ := by rw [mul_sum]
  have hcols : (∑ i ∈ S, ∑ j ∈ S, m i*m j*k i j*x j^2) ≤
      L*∑ i ∈ S, m i*x i^2 := by
    rw [sum_comm]
    convert hrows using 1
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
    ring
  have hpoint : (∑ i ∈ S, ∑ j ∈ S, 2*(m i*m j*k i j*x i*x j)) ≤
      ∑ i ∈ S, ∑ j ∈ S, (m i*m j*k i j*x i^2+m i*m j*k i j*x j^2) := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have hpos := mul_nonneg (mul_nonneg (mul_nonneg (hm i hi) (hm j hj)) (hk i hi j hj))
      (sq_nonneg (x i-x j))
    nlinarith
  simp only [← mul_sum,sum_add_distrib] at hpoint
  linarith

theorem gaussian_weighted_mean {ι : Type*} (S : Finset ι) (a : ι → ℂ) (m w : ι → ℝ)
    (b L : ℝ) (hb : 0 < b) (hm : ∀ i ∈ S, 0 ≤ m i)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, m j*Real.exp (-((w i-w j)^2/(4*b)))) ≤ L) :
    (∫ t : ℝ, Real.exp (-b*t^2)*‖polynomial S (fun i ↦ (m i : ℂ)*a i) w t‖^2) ≤
      Real.sqrt (Real.pi/b)*L*∑ i ∈ S, m i*‖a i‖^2 := by
  let c : ι → ℂ := fun i ↦ (m i : ℂ)*a i
  have hg := gaussian_gram S c w b hb
  have hi := le_abs_self (∫ t : ℝ, Real.exp (-b*t^2)*‖polynomial S c w t‖^2)
  have hn := congrArg norm hg
  simp only [Complex.norm_real,Real.norm_eq_abs] at hn
  rw [hn] at hi
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (Real.pi/b))] at hi
  have hnorm : ‖∑ i ∈ S, ∑ j ∈ S, c i*star (c j)*
      Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ))‖ ≤
      ∑ i ∈ S, ∑ j ∈ S, m i*m j*Real.exp (-((w i-w j)^2/(4*b)))*‖a i‖*‖a j‖ := by
    calc
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, c i*star (c j)*
          Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro i hiS
        calc
          _ ≤ ∑ j ∈ S, ‖c i*star (c j)*Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ))‖ := norm_sum_le _ _
          _ = _ := by
            apply sum_congr rfl
            intro j hjS
            simp only [c,norm_mul,norm_star,Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,
              Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hm i hiS),abs_of_nonneg (hm j hjS)]
            ring
  have hk := weighted_symmetric_bound S m (fun i ↦ ‖a i‖)
    (fun i j ↦ Real.exp (-((w i-w j)^2/(4*b)))) L hm
    (fun _ _ _ _ ↦ (Real.exp_pos _).le) (by
      intro i hiS j hjS
      congr 1
      ring) hrow
  exact (hi.trans (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg (Real.pi/b)))
end PaperP1.WeightedGaussianKernel
