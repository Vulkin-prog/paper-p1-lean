module

public import PaperP1.Analysis.LognormalMellinIntegral
public import PaperP1.Analysis.LognormalSumIntegrability
public import PaperP1.Analysis.LognormalPhaseVariation
public import PaperP1.Analysis.LognormalMellinError
public import PaperP1.Analysis.LognormalWeightVariation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NearLognormalKernel
open Finset Filter MeasureTheory PaperP1 LognormalPhaseVariation
open scoped Classical

def constant : ℝ := LognormalMellinError.constant+2*(LognormalWeightVariation.constant+1)

theorem constant_pos : 0 < constant := by
  have hK := LognormalMellinError.constant_pos
  have hC := LognormalWeightVariation.constant_pos
  unfold constant
  positivity

theorem difference_bound (A t : ℝ) (hA : 2 ≤ A) (ht : |t| ≤ A^(1/4 : ℝ)) :
    ‖LognormalSumIntegrability.value A t-(∫ x in Set.Ioi (0 : ℝ), function A t x)‖ ≤ constant*A^(3/4 : ℝ) := by
  have hAP : 0 < A := by linarith only [hA]
  have hA1 : 1 ≤ A := by linarith only [hA]
  have hK := LognormalMellinError.constant_pos
  have hC := LognormalWeightVariation.constant_pos
  have hInv : 1/A ≤ A^(3/4 : ℝ) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hA1
    have hPower := Real.one_le_rpow hA1 (by norm_num : (0 : ℝ) ≤ 3/4)
    norm_num only [div_one] at hh
    exact hh.trans hPower
  have hFirst : LognormalMellinError.constant/A ≤ LognormalMellinError.constant*A^(3/4 : ℝ) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hInv hK.le
  have hSqrt : Real.sqrt A ≤ A^(3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num : (1/2 : ℝ) ≤ 3/4)
  have hSecond := mul_le_mul_of_nonneg_left hSqrt hC.le
  have hMixed : |t| * Real.sqrt A ≤ A^(3/4 : ℝ) := by
    calc
      _ ≤ A^(1/4 : ℝ)*Real.sqrt A := mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg A)
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_add hAP]; norm_num
  have hError := LognormalMellinError.difference_bound A t hA
  unfold constant
  nlinarith only [hError,hFirst,hSecond,hMixed]

theorem kernel_difference_bound (A t : ℝ) (hA : 2 ≤ A) (ht : |t| ≤ A^(1/4 : ℝ)) :
    ‖LognormalSumIntegrability.value A t-
      (A : ℂ)*LogarithmicPhase.phase (-Real.log A) t*
        ((Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ)))‖ ≤ constant*A^(3/4 : ℝ) := by
  have hh := difference_bound A t hA ht
  have he : (∫ x in Set.Ioi (0 : ℝ), function A t x)=
      (A : ℂ)*LogarithmicPhase.phase (-Real.log A) t*
        ((Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ))) :=
    LognormalMellinIntegral.integral_identity A t (by linarith only [hA])
  rw [he] at hh
  exact hh

theorem value_norm_bound (A t : ℝ) (hA : 2 ≤ A) (ht : |t| ≤ A^(1/4 : ℝ)) :
    ‖LognormalSumIntegrability.value A t‖ ≤
      A*Real.sqrt Real.pi*Real.exp (-(t^2/4))+constant*A^(3/4 : ℝ) := by
  let I := ∫ x in Set.Ioi (0 : ℝ), function A t x
  have hTriangle : ‖LognormalSumIntegrability.value A t‖ ≤ ‖LognormalSumIntegrability.value A t-I‖+‖I‖ := by
    simpa only [sub_add_cancel] using norm_add_le (LognormalSumIntegrability.value A t-I) I
  have hDifference := difference_bound A t hA ht
  have hIntegral : ‖I‖=A*Real.sqrt Real.pi*Real.exp (-(t^2/4)) :=
    LognormalMellinIntegral.integral_norm A t (by linarith only [hA])
  exact hTriangle.trans ((add_le_add hDifference hIntegral.le).trans_eq (by ring))
end PaperP1.NearLognormalKernel
