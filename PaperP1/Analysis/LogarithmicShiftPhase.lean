module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicShiftPhase
open Finset MeasureTheory PaperP1 LogarithmicPhase
open scoped Classical

def function (t h x : ℝ) : ℂ :=
  LogarithmicExponentialSum.function t x*star (LogarithmicExponentialSum.function t (x+h))

theorem phase_identity (t h x : ℝ) : function t h x=phase (Real.log (x+h)-Real.log x) t := by
  rw [function,LogarithmicExponentialSum.function,LogarithmicExponentialSum.function,phase_conj,← phase_add]
  congr 1
  ring

theorem function_norm (t h x : ℝ) : ‖function t h x‖=1 := by rw [phase_identity,phase_norm]

theorem hasDerivAt_function (t h x : ℝ) (hx : 0 < x) (hxp : 0 < x+h) :
    HasDerivAt (function t h)
      (function t h x*((-Complex.I*(t : ℂ)*(h : ℂ))/((x : ℂ)*((x+h : ℝ) : ℂ)))) x := by
  have h1 := LogarithmicExponentialSum.hasDerivAt_function t x hx
  have h2 : HasDerivAt (fun y : ℝ ↦ LogarithmicExponentialSum.function t (y+h))
      (LogarithmicExponentialSum.function t (x+h)*((-Complex.I*(t : ℂ))/((x+h : ℝ) : ℂ))) x := by
    simpa only [id_eq,Function.comp_def,one_mul,mul_one,one_smul] using
      (LogarithmicExponentialSum.hasDerivAt_function t (x+h) hxp).scomp x ((hasDerivAt_id x).add_const h)
  have hh := h1.mul h2.star
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hsumC : (x : ℂ)+(h : ℂ) ≠ 0 := by exact_mod_cast hxp.ne'
  convert hh using 1
  · rfl
  · simp [function]
    field_simp [hxC,hsumC]
    ring

theorem derivative_norm (t h x : ℝ) (hx : 0 < x) (hh : 0 ≤ h) :
    ‖function t h x*((-Complex.I*(t : ℂ)*(h : ℂ))/((x : ℂ)*((x+h : ℝ) : ℂ)))‖=
      |t| * h/(x*(x+h)) := by
  have hxp : 0 < x+h := by linarith
  rw [norm_mul,function_norm,one_mul]
  simp only [norm_div,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hx,abs_of_pos hxp,abs_of_nonneg hh,one_mul]

def denominator (t h : ℝ) : ℂ := -Complex.I*(t : ℂ)*(h : ℂ)
def amplitude (t h x : ℝ) : ℂ := (x : ℂ)*((x+h : ℝ) : ℂ)/denominator t h
def amplitudeDeriv (t h x : ℝ) : ℂ := ((2*x+h : ℝ) : ℂ)/denominator t h

theorem denominator_ne (t h : ℝ) (ht : t ≠ 0) (hh : 0 < h) : denominator t h ≠ 0 := by
  unfold denominator
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast ht)) (by exact_mod_cast hh.ne')

theorem denominator_norm (t h : ℝ) (hh : 0 ≤ h) : ‖denominator t h‖=|t| * h := by
  simp only [denominator,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh,one_mul]

theorem hasDerivAt_amplitude (t h x : ℝ) : HasDerivAt (amplitude t h) (amplitudeDeriv t h x) x := by
  have hh := ((hasDerivAt_id x).ofReal_comp.mul (((hasDerivAt_id x).add_const h).ofReal_comp)).div_const (denominator t h)
  convert hh using 1
  · funext y
    rfl
  · simp only [amplitudeDeriv,id_eq,Complex.ofReal_one,one_mul,mul_one]
    push_cast
    ring

theorem amplitude_norm (t h x : ℝ) (hx : 0 < x) (hh : 0 ≤ h) :
    ‖amplitude t h x‖=x*(x+h)/(|t| * h) := by
  have hxp : 0 < x+h := by linarith
  simp only [amplitude,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,
    abs_of_pos hxp,denominator_norm t h hh]

theorem amplitudeDeriv_norm (t h x : ℝ) (hx : 0 < x) (hh : 0 ≤ h) :
    ‖amplitudeDeriv t h x‖=(2*x+h)/(|t| * h) := by
  simp only [amplitudeDeriv,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < 2*x+h),denominator_norm t h hh]

theorem derivative_amplitude_cancel (t h x : ℝ) (ht : t ≠ 0) (hh : 0 < h) (hx : 0 < x) :
    (function t h x*((-Complex.I*(t : ℂ)*(h : ℂ))/((x : ℂ)*((x+h : ℝ) : ℂ))))*amplitude t h x=function t h x := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxpC : ((x+h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show x+h ≠ 0 by linarith)
  unfold amplitude
  change function t h x*(denominator t h/((x : ℂ)*((x+h : ℝ) : ℂ)))*
    ((x : ℂ)*((x+h : ℝ) : ℂ)/denominator t h)=_
  field_simp [hxC,hxpC,denominator_ne t h ht hh]
end PaperP1.LogarithmicShiftPhase
