module

public import PaperP1.Analysis.LogarithmicShiftPhase
public import PaperP1.Analysis.IteratedLogarithmicPhase
public import PaperP1.Analysis.PositiveReciprocalKernel
public import PaperP1.Analysis.ReciprocalFiniteDifferences

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IteratedOscillationAmplitude
open PaperP1 ReciprocalFiniteDifferences IteratedLogarithmicPhase

def denominator (t : ℝ) : ℂ := -Complex.I*(t : ℂ)

def amplitude (hs : List ℝ) (t x : ℝ) : ℂ := ((1/kernel hs 1 x : ℝ) : ℂ)/denominator t

def amplitudeDeriv (hs : List ℝ) (t x : ℝ) : ℂ :=
  ((kernel hs 2 x/(kernel hs 1 x)^2 : ℝ) : ℂ)/denominator t

theorem denominator_ne (t : ℝ) (ht : t ≠ 0) : denominator t ≠ 0 := by
  unfold denominator
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast ht)

theorem denominator_norm (t : ℝ) : ‖denominator t‖=|t| := by
  simp only [denominator,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]

theorem hasDerivAt_amplitude (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t x : ℝ) (hx : 0 < x) :
    HasDerivAt (amplitude hs t) (amplitudeDeriv hs t x) x :=
  (PositiveReciprocalKernel.inverse_first_hasDerivAt hs hhs x hx).ofReal_comp.div_const (denominator t)

theorem amplitude_norm (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t x : ℝ) (hx : 0 < x) :
    ‖amplitude hs t x‖=(1/kernel hs 1 x)/|t| := by
  have hK := PositiveReciprocalKernel.kernel_pos hs hhs 1 (by norm_num) x hx
  have hInv : 0 < 1/kernel hs 1 x := by positivity
  rw [amplitude,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hInv,denominator_norm]

theorem amplitudeDeriv_norm (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (t x : ℝ) (hx : 0 < x) :
    ‖amplitudeDeriv hs t x‖=(kernel hs 2 x/(kernel hs 1 x)^2)/|t| := by
  have hNN := PositiveReciprocalKernel.inverse_derivative_nonneg hs hhs x hx
  rw [amplitudeDeriv,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hNN,denominator_norm]

theorem derivative_amplitude_cancel (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t x : ℝ)
    (ht : t ≠ 0) (hx : 0 < x) :
    (function hs t x*((-Complex.I*(t : ℂ))*(kernel hs 1 x : ℂ)))*amplitude hs t x=function hs t x := by
  have hK := PositiveReciprocalKernel.kernel_pos hs hhs 1 (by norm_num) x hx
  have hKC : (kernel hs 1 x : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  unfold amplitude denominator
  push_cast
  field_simp [hKC,htC,Complex.I_ne_zero]

theorem product_hasDeriv (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (t x : ℝ)
    (ht : t ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ function hs t y*amplitude hs t y)
      (function hs t x+function hs t x*amplitudeDeriv hs t x) x := by
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hp := (hasDerivAt_function hs hNN t x hx).mul (hasDerivAt_amplitude hs hhs t x hx)
  convert hp using 1
  rw [derivative_amplitude_cancel hs hhs t x ht hx]
end PaperP1.IteratedOscillationAmplitude
