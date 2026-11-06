module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! # Exact logarithmic phases, oscillatory interval integrals and the real Gaussian transform -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicPhase
open Complex Finset MeasureTheory

def phase (w t : ℝ) : ℂ := Complex.exp (Complex.I * (w : ℂ) * (t : ℂ))

theorem phase_zero (t : ℝ) : phase 0 t = 1 := by simp [phase]

theorem phase_add (w μ t : ℝ) : phase (w+μ) t = phase w t * phase μ t := by
  unfold phase
  rw [Complex.ofReal_add, mul_add, add_mul, Complex.exp_add]

theorem phase_conj (w t : ℝ) : star (phase w t) = phase (-w) t := by
  unfold phase
  change (starRingEnd ℂ) (Complex.exp (Complex.I * (w : ℂ) * (t : ℂ))) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem phase_norm (w t : ℝ) : ‖phase w t‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

theorem phase_continuous (w : ℝ) : Continuous (phase w) := by unfold phase; fun_prop

theorem phase_mul_log (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    phase (Real.log (m*n : ℕ)) t = phase (Real.log m) t * phase (Real.log n) t := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast Nat.ne_of_gt hm) (by exact_mod_cast Nat.ne_of_gt hn), phase_add]

theorem interval_integral (w A B : ℝ) (hw : w ≠ 0) :
    (∫ t in A..B, phase w t) = (phase w B - phase w A) / (Complex.I * (w : ℂ)) := by
  exact integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hw))

theorem interval_integral_norm (w A B : ℝ) (hw : w ≠ 0) :
    ‖∫ t in A..B, phase w t‖ ≤ 2 / |w| := by
  rw [interval_integral w A B hw, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg w)
  exact (norm_sub_le _ _).trans (by rw [phase_norm, phase_norm]; norm_num)

theorem gaussian_integral (b w : ℝ) (hb : 0 < b) :
    (∫ t : ℝ, phase w t * Complex.exp (-(b : ℂ) * (t : ℂ)^2)) =
      (Real.sqrt (Real.pi / b) : ℂ) * Complex.exp (-((w^2 / (4*b) : ℝ) : ℂ)) := by
  have hh := fourierIntegral_gaussian (b := (b : ℂ)) (by simpa only [Complex.ofReal_re] using hb) (w : ℂ)
  simpa only [phase, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_neg, neg_div, Real.sqrt_eq_rpow,
    Complex.ofReal_cpow (by positivity : 0 ≤ Real.pi / b)] using hh
end LogarithmicPhase
