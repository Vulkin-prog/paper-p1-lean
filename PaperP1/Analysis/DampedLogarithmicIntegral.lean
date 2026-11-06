module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DampedLogarithmicIntegral
open Finset Filter MeasureTheory PaperP1
open scoped Classical

def denominator (σ t : ℝ) : ℂ := -(σ : ℂ)-Complex.I*(t : ℂ)

def numerator (σ t x : ℝ) : ℂ := ((x^(-σ) : ℝ) : ℂ)*LogarithmicExponentialSum.function t x

def integrand (σ t x : ℝ) : ℂ := numerator σ t x/(x : ℂ)

theorem denominator_norm_lower (σ t : ℝ) : |t| ≤ ‖denominator σ t‖ := by
  simpa [denominator] using Complex.abs_im_le_norm (denominator σ t)

theorem denominator_ne (σ t : ℝ) (ht : t ≠ 0) : denominator σ t ≠ 0 := by
  have hp := abs_pos.mpr ht
  exact norm_pos_iff.mp (hp.trans_le (denominator_norm_lower σ t))

theorem numerator_norm (σ t x : ℝ) (hx : 0 < x) : ‖numerator σ t x‖=x^(-σ) := by
  rw [numerator,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hx (-σ)),LogarithmicExponentialSum.function_norm,mul_one]

theorem hasDerivAt_numerator (σ t x : ℝ) (hx : 0 < x) :
    HasDerivAt (numerator σ t) (denominator σ t*integrand σ t x) x := by
  have hPow := (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hx.ne')).ofReal_comp
  have hh := hPow.mul (LogarithmicExponentialSum.hasDerivAt_function t x hx)
  have hPower : x^(-σ-1)=x^(-σ)/x := by rw [Real.rpow_sub hx,Real.rpow_one]
  convert hh using 1
  · rfl
  · unfold denominator integrand numerator
    rw [hPower]
    push_cast
    ring

theorem continuousOn_numerator (σ t A B : ℝ) (hA : 0 < A) :
    ContinuousOn (numerator σ t) (Set.Icc A B) := by
  intro x hx
  exact (hasDerivAt_numerator σ t x (hA.trans_le hx.1)).continuousAt.continuousWithinAt

theorem continuousOn_integrand (σ t A B : ℝ) (hA : 0 < A) :
    ContinuousOn (integrand σ t) (Set.Icc A B) := by
  unfold integrand
  exact (continuousOn_numerator σ t A B hA).div
    (Complex.continuous_ofReal.comp_continuousOn continuousOn_id)
    (fun x hx ↦ by exact_mod_cast (hA.trans_le hx.1).ne')

theorem integral_identity (σ t A B : ℝ) (ht : t ≠ 0) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, integrand σ t x)=
      (numerator σ t B-numerator σ t A)/denominator σ t := by
  have hD := denominator_ne σ t ht
  have hInt : IntervalIntegrable (integrand σ t) volume A B :=
    (continuousOn_integrand σ t A B hA).intervalIntegrable_of_Icc hAB
  have hh : (∫ x in A..B, integrand σ t x)=
      numerator σ t B/denominator σ t-numerator σ t A/denominator σ t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hAB] at hx
      have hd := (hasDerivAt_numerator σ t x (hA.trans_le hx.1)).div_const (denominator σ t)
      simpa only [mul_div_cancel_left₀ _ hD] using hd
    · exact hInt
  simpa only [sub_div] using hh

theorem integral_norm_bound (σ t A B : ℝ) (hσ : 0 ≤ σ) (ht : t ≠ 0)
    (hA : 0 < A) (hAB : A ≤ B) :
    ‖∫ x in A..B, integrand σ t x‖ ≤ 2*A^(-σ)/|t| := by
  have hB : 0 < B := hA.trans_le hAB
  have hPow := Real.rpow_le_rpow_of_nonpos hA hAB (neg_nonpos.mpr hσ)
  rw [integral_identity σ t A B ht hA hAB,norm_div]
  calc
    _ ≤ (‖numerator σ t B‖+‖numerator σ t A‖)/‖denominator σ t‖ :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ = (B^(-σ)+A^(-σ))/‖denominator σ t‖ := by rw [numerator_norm σ t B hB,numerator_norm σ t A hA]
    _ ≤ (2*A^(-σ))/‖denominator σ t‖ :=
      div_le_div_of_nonneg_right (by linarith only [hPow]) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr ht) (denominator_norm_lower σ t)
end PaperP1.DampedLogarithmicIntegral
