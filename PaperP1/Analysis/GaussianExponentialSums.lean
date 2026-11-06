module

public import PaperP1.Analysis.LogarithmicPhase
public import PaperP1.Analysis.FiniteSymmetricKernelBudget

/-! # Exact finite Gaussian Gram identities and actual exponential-sum mean-square bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GaussianExponentialSums
open Finset Complex MeasureTheory PaperP1.LogarithmicPhase
open scoped Classical ComplexConjugate

def polynomial {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i * phase (w i) t

theorem polynomial_continuous {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ) :
    Continuous (polynomial S a w) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (phase_continuous (w i))

theorem polynomial_norm_bound {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (t : ℝ) :
    ‖polynomial S a w t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i * phase (w i) t‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, phase_norm, mul_one]

theorem gaussian_integrable {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ)
    (b : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ ↦ Real.exp (-b*t^2) * ‖polynomial S a w t‖^2) := by
  have hd := (integrable_exp_neg_mul_sq hb).mul_const ((∑ i ∈ S, ‖a i‖)^2)
  have hp := polynomial_continuous S a w
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-b*t^2) * ‖polynomial S a w t‖^2) := by fun_prop
  apply hd.mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hh := polynomial_norm_bound S a w t
  have hn := norm_nonneg (polynomial S a w t)
  nlinarith

theorem interval_le_gaussian {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ)
    (b T : ℝ) (hb : 0 < b) (hT : 0 < T) :
    (∫ t in -T..T, ‖polynomial S a w t‖^2) ≤
      Real.exp (b*T^2) * (∫ t : ℝ, Real.exp (-b*t^2) * ‖polynomial S a w t‖^2) := by
  have hp := polynomial_continuous S a w
  have hc1 : Continuous (fun t : ℝ ↦ ‖polynomial S a w t‖^2) := by fun_prop
  have hc2 : Continuous (fun t : ℝ ↦ Real.exp (b*T^2) *
      (Real.exp (-b*t^2) * ‖polynomial S a w t‖^2)) := by fun_prop
  calc
    _ ≤ ∫ t in -T..T, Real.exp (b*T^2) *
        (Real.exp (-b*t^2) * ‖polynomial S a w t‖^2) := by
      apply intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable (-T) T) (hc2.intervalIntegrable (-T) T)
      intro t ht
      have hsq : t^2 ≤ T^2 := by nlinarith [ht.1, ht.2]
      have hf : 1 ≤ Real.exp (b*T^2) * Real.exp (-b*t^2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      nlinarith [sq_nonneg ‖polynomial S a w t‖]
    _ = Real.exp (b*T^2) * (∫ t in -T..T, Real.exp (-b*t^2) * ‖polynomial S a w t‖^2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral (gaussian_integrable S a w b hb)
        (Filter.Eventually.of_forall (fun _ ↦ mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

theorem norm_square_expansion {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (t : ℝ) :
    ((‖polynomial S a w t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, a i * star (a j) * phase (w i - w j) t := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold polynomial
  rw [map_sum, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [map_mul]
  change a i * phase (w i) t * (star (a j) * star (phase (w j) t)) = _
  rw [phase_conj, sub_eq_add_neg, phase_add]
  ring

theorem gaussian_cross_integrable (b u v : ℝ) (hb : 0 < b) :
    Integrable (fun t : ℝ ↦ phase (u-v) t * Complex.exp (-(b : ℂ)*(t : ℂ)^2)) := by
  have hh := integrable_cexp_quadratic (b := (b : ℂ)) (by simpa only [Complex.ofReal_re] using hb)
    (Complex.I * ((u-v : ℝ) : ℂ)) 0
  convert hh using 1
  funext t
  rw [phase, ← Complex.exp_add]
  congr 1
  ring

theorem gaussian_gram {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ)
    (b : ℝ) (hb : 0 < b) :
    ((∫ t : ℝ, Real.exp (-b*t^2) * ‖polynomial S a w t‖^2 : ℝ) : ℂ) =
      (Real.sqrt (Real.pi / b) : ℂ) *
        ∑ i ∈ S, ∑ j ∈ S, a i * star (a j) *
          Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ)) := by
  have hpoint (t : ℝ) :
      ((Real.exp (-b*t^2) * ‖polynomial S a w t‖^2 : ℝ) : ℂ) =
        ∑ i ∈ S, ∑ j ∈ S, (a i * star (a j)) *
          (phase (w i-w j) t * Complex.exp (-(b : ℂ)*(t : ℂ)^2)) := by
    rw [Complex.ofReal_mul, norm_square_expansion, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [Complex.ofReal_exp]
    push_cast
    ring
  rw [← integral_complex_ofReal]
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [integral_const_mul, gaussian_integral b (w i-w j) hb]
      ring
    · intro j hj
      exact (gaussian_cross_integrable b (w i) (w j) hb).const_mul _
  · intro i hi
    exact integrable_finsetSum S (fun j hj ↦
      (gaussian_cross_integrable b (w i) (w j) hb).const_mul _)
theorem gaussian_mean_square_le {ι : Type*} (S : Finset ι) (a : ι → ℂ) (w : ι → ℝ)
    (b L : ℝ) (hb : 0 < b)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, Real.exp (-((w i-w j)^2/(4*b)))) ≤ L) :
    (∫ t : ℝ, Real.exp (-b*t^2) * ‖polynomial S a w t‖^2) ≤
      Real.sqrt (Real.pi / b) * L * ∑ i ∈ S, ‖a i‖^2 := by
  have hg := gaussian_gram S a w b hb
  have hi := le_abs_self (∫ t : ℝ, Real.exp (-b*t^2) * ‖polynomial S a w t‖^2)
  have hn := congrArg norm hg
  simp only [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn] at hi
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (Real.pi / b))] at hi
  have hnorm : ‖∑ i ∈ S, ∑ j ∈ S, a i * star (a j) *
      Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ))‖ ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ * Real.exp (-((w i-w j)^2/(4*b))) := by
    calc
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, a i * star (a j) *
          Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ))‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        calc
          _ ≤ ∑ j ∈ S, ‖a i * star (a j) *
              Complex.exp (-(((w i-w j)^2/(4*b) : ℝ) : ℂ))‖ := norm_sum_le _ _
          _ = _ := by
            apply sum_congr rfl
            intro j hj
            simp only [norm_mul, norm_star, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
  have hk := PaperP1.FiniteSymmetricKernelBudget.symmetric_bound S (fun i ↦ ‖a i‖)
    (fun i j ↦ Real.exp (-((w i-w j)^2/(4*b)))) L
    (fun _ _ _ _ ↦ (Real.exp_pos _).le) (by
      intro i hi j hj
      congr 1
      ring) hrow
  have hk' : (∑ i ∈ S, ∑ j ∈ S, ‖a i‖ * ‖a j‖ * Real.exp (-((w i-w j)^2/(4*b)))) ≤
      L * ∑ i ∈ S, ‖a i‖^2 := by
    convert hk using 1
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  exact (hi.trans (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _))).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hk' (Real.sqrt_nonneg (Real.pi / b)))

end GaussianExponentialSums
