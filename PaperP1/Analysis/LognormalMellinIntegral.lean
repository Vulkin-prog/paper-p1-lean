module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.LogarithmicPhase
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalMellinIntegral
open Finset Filter MeasureTheory PaperP1 LogarithmicPhase LognormalSieveWeight
open scoped Classical

def kernel (t y : ℝ) : ℂ := (Real.exp (-y^2) : ℂ)*phase (-t) y

theorem phase_neg_swap (y t : ℝ) : phase (-y) t=phase (-t) y := by
  unfold phase
  congr 1
  push_cast
  ring

theorem kernel_integral (t : ℝ) :
    (∫ y : ℝ, kernel t y)=(Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ)) := by
  have he : (fun y : ℝ ↦ kernel t y)=
      (fun y : ℝ ↦ phase (-t) y*Complex.exp (-(y : ℂ)^2)) := by
    funext y
    unfold kernel
    rw [Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_pow]
    ring
  rw [he]
  have hh := LogarithmicPhase.gaussian_integral 1 (-t) (by norm_num)
  simpa only [Complex.ofReal_one,neg_one_mul,div_one,mul_one,one_mul,neg_sq] using hh

theorem phase_log_identity (A x t : ℝ) (hA : 0 < A) (hx : 0 < x) :
    phase (-Real.log x) t=phase (-Real.log A) t*phase (-t) (Real.log (x/A)) := by
  have hh := phase_add (-Real.log A) (-Real.log (x/A)) t
  have he : -Real.log A+-Real.log (x/A)=-Real.log x := by
    rw [Real.log_div hx.ne' hA.ne']
    ring
  rw [he,phase_neg_swap (Real.log (x/A)) t] at hh
  exact hh

theorem integrand_identity (A x t : ℝ) (hA : 0 < A) (hx : 0 < x) :
    (weight A x : ℂ)*LogarithmicExponentialSum.function t x=
      x⁻¹ • ((A : ℂ)*phase (-Real.log A) t*kernel t (Real.log x-Real.log A)) := by
  rw [gaussian_identity A x hA hx,Complex.ofReal_mul,LogarithmicExponentialSum.function,
    phase_log_identity A x t hA hx]
  unfold kernel
  rw [Real.log_div hx.ne' hA.ne',RCLike.real_smul_eq_coe_mul]
  push_cast
  simp only [div_eq_mul_inv]
  ac_rfl

theorem integral_identity (A t : ℝ) (hA : 0 < A) :
    (∫ x in Set.Ioi (0 : ℝ), (weight A x : ℂ)*LogarithmicExponentialSum.function t x)=
      (A : ℂ)*phase (-Real.log A) t*((Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ))) := by
  have he : (∫ x in Set.Ioi (0 : ℝ), (weight A x : ℂ)*LogarithmicExponentialSum.function t x)=
      ∫ x in Set.Ioi (0 : ℝ), x⁻¹ • ((A : ℂ)*phase (-Real.log A) t*kernel t (Real.log x-Real.log A)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact integrand_identity A x t hA hx
  rw [he]
  have hShift : (∫ y : ℝ, kernel t (y-Real.log A))=∫ y : ℝ, kernel t y := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (kernel t) (-Real.log A)
  calc
    _ = ∫ y : ℝ, (A : ℂ)*phase (-Real.log A) t*kernel t (y-Real.log A) :=
      MeasureTheory.integral_comp_log_Ioi_zero (fun y : ℝ ↦ (A : ℂ)*phase (-Real.log A) t*kernel t (y-Real.log A))
    _ = _ := by rw [integral_const_mul,hShift,kernel_integral]

theorem integral_norm (A t : ℝ) (hA : 0 < A) :
    ‖∫ x in Set.Ioi (0 : ℝ), (weight A x : ℂ)*LogarithmicExponentialSum.function t x‖=
      A*Real.sqrt Real.pi*Real.exp (-(t^2/4)) := by
  rw [integral_identity A t hA]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA,phase_norm,
    Complex.norm_exp,Complex.neg_re,Complex.ofReal_re,abs_of_nonneg (Real.sqrt_nonneg _),mul_one]
  ring
end PaperP1.LognormalMellinIntegral
