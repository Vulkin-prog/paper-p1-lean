module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.GaussianSlopeDecay
public import PaperP1.Analysis.LognormalSieveWeight

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalWeightVariation
open PaperP1 LognormalSieveWeight

def constant : ℝ := 2*Real.exp 2

theorem constant_pos : 0 < constant := by unfold constant; positivity

theorem weight_le_ratio (A x : ℝ) (hA : 0 < A) (hx : 0 < x) : weight A x ≤ A/x := by
  rw [gaussian_identity A x hA hx]
  have hh := mul_le_mul_of_nonneg_left (GaussianSlopeDecay.gaussian_le_one (Real.log (x/A))) (div_nonneg hA.le hx.le)
  simpa only [mul_one] using hh

theorem derivative_abs_bound (A x : ℝ) (hA : 0 < A) (hx : 0 < x) :
    |weight A x*(-(1+2*Real.log (x/A))/x)| ≤ constant*A/x^2 := by
  have hAbs : |1+2*Real.log (x/A)| ≤ 1+2*|Real.log (x/A)| := by
    have hh := norm_add_le (1 : ℝ) (2*Real.log (x/A))
    simpa only [Real.norm_eq_abs,abs_one,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh
  have hScalar : |1+2*Real.log (x/A)| * Real.exp (-(Real.log (x/A))^2) ≤ constant :=
    (mul_le_mul_of_nonneg_right hAbs (Real.exp_pos _).le).trans
      (GaussianSlopeDecay.slope_uniform_bound (Real.log (x/A)))
  calc
    _ = (A/x^2)*(|1+2*Real.log (x/A)| * Real.exp (-(Real.log (x/A))^2)) := by
      rw [abs_mul,abs_of_pos (weight_pos A x),abs_div,abs_neg,abs_of_pos hx,gaussian_identity A x hA hx]
      ring
    _ ≤ (A/x^2)*constant := mul_le_mul_of_nonneg_left hScalar (by positivity)
    _ = _ := by ring

theorem derivative_uniform_bound (A N x : ℝ) (hA : 0 < A) (hN : 0 < N) (hNx : N ≤ x) :
    |weight A x*(-(1+2*Real.log (x/A))/x)| ≤ constant*A/N^2 := by
  have hx : 0 < x := hN.trans_le hNx
  exact (derivative_abs_bound A x hA hx).trans (div_le_div_of_nonneg_left
    (mul_nonneg constant_pos.le hA.le) (sq_pos_of_pos hN) (pow_le_pow_left₀ hN.le hNx 2))

theorem local_variation (A N x : ℝ) (hA : 0 < A) (hN : 0 < N) (hx : x ∈ Set.Icc N (N+1)) :
    |weight A x-weight A N| ≤ constant*A/N^2 := by
  have hDer : ∀ y ∈ Set.Icc N (N+1), HasDerivWithinAt (weight A)
      (weight A y*(-(1+2*Real.log (y/A))/y)) (Set.Icc N (N+1)) y :=
    fun y hy ↦ (hasDerivAt_weight A y hA (hN.trans_le hy.1)).hasDerivWithinAt
  have hBound : ∀ y ∈ Set.Ico N (N+1),
      ‖weight A y*(-(1+2*Real.log (y/A))/y)‖ ≤ constant*A/N^2 := by
    intro y hy
    rw [Real.norm_eq_abs]
    exact derivative_uniform_bound A N y hA hN hy.1
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hDer hBound x hx
  have hLen : x-N ≤ 1 := by linarith only [hx.2]
  rw [Real.norm_eq_abs] at hh
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hLen (by have hc := constant_pos; positivity : 0 ≤ constant*A/N^2))
end PaperP1.LognormalWeightVariation
