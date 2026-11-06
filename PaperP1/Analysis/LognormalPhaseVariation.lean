module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.LognormalWeightVariation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalPhaseVariation
open Finset Filter MeasureTheory PaperP1 LognormalSieveWeight
open scoped Classical

def function (A t x : ℝ) : ℂ := (weight A x : ℂ)*LogarithmicExponentialSum.function t x

def derivative (A t x : ℝ) : ℂ :=
  ((weight A x*(-(1+2*Real.log (x/A))/x) : ℝ) : ℂ)*LogarithmicExponentialSum.function t x+
    (weight A x : ℂ)*(LogarithmicExponentialSum.function t x*((-Complex.I*(t : ℂ))/(x : ℂ)))

theorem function_norm (A t x : ℝ) : ‖function A t x‖=weight A x := by
  rw [function,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A x),LogarithmicExponentialSum.function_norm,mul_one]

theorem hasDerivAt_function (A t x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    HasDerivAt (function A t) (derivative A t x) x := by
  exact ((hasDerivAt_weight A x hA hx).ofReal_comp).mul
    (LogarithmicExponentialSum.hasDerivAt_function t x hx)

theorem derivative_norm_bound (A t x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    ‖derivative A t x‖ ≤ (LognormalWeightVariation.constant+|t|)*A/x^2 := by
  have hFirst : ‖((weight A x*(-(1+2*Real.log (x/A))/x) : ℝ) : ℂ)*
      LogarithmicExponentialSum.function t x‖ ≤ LognormalWeightVariation.constant*A/x^2 := by
    rw [norm_mul,LogarithmicExponentialSum.function_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]
    exact LognormalWeightVariation.derivative_abs_bound A x hA hx
  have hSecond : ‖(weight A x : ℂ)*(LogarithmicExponentialSum.function t x*((-Complex.I*(t : ℂ))/(x : ℂ)))‖ ≤
      |t| * A/x^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A x),LogarithmicExponentialSum.derivative_norm t x hx]
    have hh := mul_le_mul_of_nonneg_right (LognormalWeightVariation.weight_le_ratio A x hA hx)
      (div_nonneg (abs_nonneg t) hx.le)
    exact hh.trans_eq (by ring)
  exact (norm_add_le _ _).trans ((add_le_add hFirst hSecond).trans_eq (by ring))

theorem derivative_uniform_bound (A t N x : ℝ) (hA : 0 < A) (hN : 0 < N) (hNx : N ≤ x) :
    ‖derivative A t x‖ ≤ (LognormalWeightVariation.constant+|t|)*A/N^2 := by
  have hc := LognormalWeightVariation.constant_pos
  exact (derivative_norm_bound A t x hA (hN.trans_le hNx)).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hN) (pow_le_pow_left₀ hN.le hNx 2))

theorem continuousOn_function (A t N M : ℝ) (hA : 0 < A) (hN : 0 < N) :
    ContinuousOn (function A t) (Set.Icc N M) := by
  intro x hx
  exact (hasDerivAt_function A t x hA (hN.trans_le hx.1)).continuousAt.continuousWithinAt

theorem local_variation (A t N x : ℝ) (hA : 0 < A) (hN : 0 < N) (hx : x ∈ Set.Icc N (N+1)) :
    ‖function A t x-function A t N‖ ≤ (LognormalWeightVariation.constant+|t|)*A/N^2 := by
  have hDer : ∀ y ∈ Set.Icc N (N+1), HasDerivWithinAt (function A t) (derivative A t y) (Set.Icc N (N+1)) y :=
    fun y hy ↦ (hasDerivAt_function A t y hA (hN.trans_le hy.1)).hasDerivWithinAt
  have hBound : ∀ y ∈ Set.Ico N (N+1), ‖derivative A t y‖ ≤
      (LognormalWeightVariation.constant+|t|)*A/N^2 :=
    fun y hy ↦ derivative_uniform_bound A t N y hA hN hy.1
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hDer hBound x hx
  have hLen : x-N ≤ 1 := by linarith only [hx.2]
  have hc := LognormalWeightVariation.constant_pos
  have hScale := mul_le_mul_of_nonneg_left hLen
    (by positivity : 0 ≤ (LognormalWeightVariation.constant+|t|)*A/N^2)
  exact hh.trans (by simpa only [mul_one] using hScale)

theorem unit_integral_error (A t N : ℝ) (hA : 0 < A) (hN : 0 < N) :
    ‖function A t N-(∫ x in N..N+1, function A t x)‖ ≤
      (LognormalWeightVariation.constant+|t|)*A/N^2 := by
  have hi : IntervalIntegrable (function A t) volume N (N+1) :=
    (continuousOn_function A t N (N+1) hA hN).intervalIntegrable_of_Icc (by linarith)
  have he : function A t N-(∫ x in N..N+1, function A t x)=
      ∫ x in N..N+1, function A t N-function A t x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi]
    simp
  rw [he]
  have hh := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by linarith : N ≤ N+1)
    (f := fun x ↦ function A t N-function A t x)
    (g := fun _ ↦ (LognormalWeightVariation.constant+|t|)*A/N^2)
    (Filter.Eventually.of_forall (fun x hx ↦ by
      rw [norm_sub_rev]
      exact local_variation A t N x hA hN ⟨hx.1.le,hx.2⟩)) intervalIntegrable_const
  simpa using hh
end PaperP1.LognormalPhaseVariation
