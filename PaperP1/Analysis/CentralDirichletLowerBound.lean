module

public import PaperP1.Analysis.CenteredLogarithmicSampling
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CentralDirichletLowerBound
open Finset PaperP1 LogarithmicPhase GaussianExponentialSums
open scoped Classical

theorem phase_re (w t : ℝ) : (phase w t).re=Real.cos (w*t) := by
  rw [phase,Complex.exp_re]
  simp

theorem reciprocal_mass_lower (N : ℕ) (hN : 0 < N) :
    (1/2 : ℝ) ≤ ∑ n ∈ Ico N (2*N), 1/(n : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (Ico N (2*N)).card=N := by simp only [Nat.card_Ico]; omega
  calc
    (1/2 : ℝ) = ∑ _n ∈ Ico N (2*N), 1/(2*(N : ℝ)) := by
      rw [sum_const,nsmul_eq_mul,hc]
      field_simp
    _ ≤ _ := sum_le_sum (fun n hn ↦ by
      have hm := mem_Ico.mp hn
      have hnp : (0 : ℝ) < n := by exact_mod_cast (hN.trans_le hm.1)
      exact one_div_le_one_div_of_le hnp (by exact_mod_cast hm.2.le))

theorem central_norm_lower (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : |t| ≤ 1/2) :
    (1/4 : ℝ) ≤ ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  let w := fun n : ℕ ↦ Real.log (N : ℝ)-Real.log (n : ℝ)
  let Z := polynomial (Ico N (2*N)) (fun n ↦ (1 : ℂ)/(n : ℂ)) w t
  have hw (n : ℕ) (hn : n ∈ Ico N (2*N)) : |w n| ≤ 1 := by
    have hm := mem_Ico.mp hn
    have hh := CenteredLogarithmicSampling.logarithmic_bandwidth (N : ℝ) (2*(N : ℝ)) (n : ℝ)
      hNp (by exact_mod_cast hm.1) (by exact_mod_cast hm.2.le)
    have hlog : Real.log (2*(N : ℝ))-Real.log (N : ℝ)=Real.log 2 := by
      rw [Real.log_mul (by norm_num) hNp.ne']
      ring
    rw [hlog] at hh
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num only [show (2 : ℝ)-1=1 by norm_num] at hlog2
    exact hh.trans hlog2
  have hterm (n : ℕ) (hn : n ∈ Ico N (2*N)) :
      (1/2 : ℝ)*(1/(n : ℝ)) ≤ (((1 : ℂ)/(n : ℂ))*phase (w n) t).re := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast (hN.trans_le (mem_Ico.mp hn).1)
    have harg : |w n*t| ≤ 1/2 := by
      rw [abs_mul]
      have hh := mul_le_mul (hw n hn) ht (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using hh
    have hsq : (w n*t)^2 ≤ (1/2 : ℝ)^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (w n*t)) (by norm_num : (0 : ℝ) ≤ 1/2)).mpr harg
      simpa only [sq_abs] using hh
    have hcos : (1/2 : ℝ) ≤ Real.cos (w n*t) := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := w n*t)
      nlinarith only [hsq,hh]
    have he : (1 : ℂ)/(n : ℂ)=((1/(n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [he]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,phase_re]
    have hh := mul_le_mul_of_nonneg_right hcos (by positivity : (0 : ℝ) ≤ 1/(n : ℝ))
    nlinarith only [hh]
  have hRe : (1/4 : ℝ) ≤ Z.re := by
    have hmap : Z.re=∑ n ∈ Ico N (2*N), (((1 : ℂ)/(n : ℂ))*phase (w n) t).re :=
      map_sum Complex.reCLM _ _
    rw [hmap]
    calc
      (1/4 : ℝ) ≤ (1/2 : ℝ)*(∑ n ∈ Ico N (2*N), 1/(n : ℝ)) := by
        have hh := mul_le_mul_of_nonneg_left (reciprocal_mass_lower N hN) (by norm_num : (0 : ℝ) ≤ 1/2)
        nlinarith only [hh]
      _ = ∑ n ∈ Ico N (2*N), (1/2 : ℝ)*(1/(n : ℝ)) := mul_sum _ _ _
      _ ≤ _ := sum_le_sum hterm
  have hnorm : ‖Z‖=‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun _ ↦ (1 : ℂ)) t‖ := by
    simpa only [Z,w,DirichletPolynomialMeanValue.value,sub_eq_add_neg] using
      CenteredLogarithmicSampling.shift_norm (Ico N (2*N)) (fun n ↦ (1 : ℂ)/(n : ℂ))
        (fun n ↦ -Real.log (n : ℝ)) (Real.log (N : ℝ)) t
  exact (hRe.trans (Complex.re_le_norm Z)).trans_eq hnorm
end PaperP1.CentralDirichletLowerBound
