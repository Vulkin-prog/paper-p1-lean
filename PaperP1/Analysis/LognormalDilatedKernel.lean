module

public import PaperP1.Analysis.NearLognormalKernel


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalDilatedKernel
open Finset Filter PaperP1
open scoped Classical

def multipleValue (A t D : ℝ) : ℂ :=
  ∑' n : ℕ, LognormalPhaseVariation.function A t (D*((n+1 : ℕ) : ℝ))

def mainValue (A t : ℝ) : ℂ :=
  (A : ℂ)*LogarithmicExponentialSum.function t A*
    ((Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ)))

theorem weight_dilation (A D x : ℝ) (hA : 0 < A) (hD : 0 < D) :
    LognormalSieveWeight.weight A (D*x)=LognormalSieveWeight.weight (A/D) x := by
  have hRatio : D*x/A=x/(A/D) := by field_simp [hA.ne',hD.ne']
  unfold LognormalSieveWeight.weight
  rw [hRatio]

theorem phase_dilation (t D x : ℝ) (hD : 0 < D) (hx : 0 < x) :
    LogarithmicExponentialSum.function t (D*x)=
      LogarithmicExponentialSum.function t D*LogarithmicExponentialSum.function t x := by
  simp only [LogarithmicExponentialSum.function,Real.log_mul hD.ne' hx.ne',neg_add,
    LogarithmicPhase.phase_add]

theorem function_dilation (A t D x : ℝ) (hA : 0 < A) (hD : 0 < D) (hx : 0 < x) :
    LognormalPhaseVariation.function A t (D*x)=
      LogarithmicExponentialSum.function t D*LognormalPhaseVariation.function (A/D) t x := by
  unfold LognormalPhaseVariation.function
  rw [weight_dilation A D x hA hD,phase_dilation t D x hD hx]
  ring

theorem summable_terms (A t D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    Summable (fun n : ℕ ↦ LognormalPhaseVariation.function A t (D*((n+1 : ℕ) : ℝ))) := by
  have hh := (LognormalSumIntegrability.summable_terms (A/D) t (div_pos hA hD)).mul_left
    (LogarithmicExponentialSum.function t D)
  apply hh.congr
  intro n
  exact (function_dilation A t D _ hA hD (by exact_mod_cast (show 0 < n+1 by omega))).symm

theorem value_dilation (A t D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    multipleValue A t D=LogarithmicExponentialSum.function t D*LognormalSumIntegrability.value (A/D) t := by
  unfold multipleValue LognormalSumIntegrability.value
  calc
    _ = ∑' n : ℕ, LogarithmicExponentialSum.function t D*
        LognormalPhaseVariation.function (A/D) t ((n+1 : ℕ) : ℝ) := by
      apply tsum_congr
      intro n
      exact function_dilation A t D _ hA hD (by exact_mod_cast (show 0 < n+1 by omega))
    _ = _ := tsum_mul_left

theorem main_dilation (A t D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    LogarithmicExponentialSum.function t D*mainValue (A/D) t=(1/D : ℝ)*mainValue A t := by
  have hPhase : LogarithmicExponentialSum.function t D*LogarithmicExponentialSum.function t (A/D)=
      LogarithmicExponentialSum.function t A := by
    rw [← phase_dilation t D (A/D) hD (div_pos hA hD)]
    congr 1
    field_simp [hD.ne']
  unfold mainValue
  calc
    _ = ((A/D : ℝ) : ℂ)*(LogarithmicExponentialSum.function t D*LogarithmicExponentialSum.function t (A/D))*
        ((Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ))) := by ring
    _ = ((A/D : ℝ) : ℂ)*LogarithmicExponentialSum.function t A*
        ((Real.sqrt Real.pi : ℂ)*Complex.exp (-((t^2/4 : ℝ) : ℂ))) := by rw [hPhase]
    _ = _ := by push_cast; simp only [div_eq_mul_inv]; ring

theorem near_bound (A t D : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hScale : 2 ≤ A/D) (ht : |t| ≤ (A/D)^(1/4 : ℝ)) :
    ‖multipleValue A t D-(1/D : ℝ)*mainValue A t‖ ≤
      NearLognormalKernel.constant*(A/D)^(3/4 : ℝ) := by
  rw [value_dilation A t D hA hD,← main_dilation A t D hA hD,← mul_sub,
    norm_mul,LogarithmicExponentialSum.function_norm,one_mul]
  exact NearLognormalKernel.kernel_difference_bound (A/D) t hScale ht
end PaperP1.LognormalDilatedKernel
