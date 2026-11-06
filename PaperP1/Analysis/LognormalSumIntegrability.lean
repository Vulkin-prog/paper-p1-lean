module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.PowerSeriesTail
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import PaperP1.Analysis.LognormalMellinIntegral

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalSumIntegrability
open Finset Filter MeasureTheory PaperP1 LogarithmicPhase LognormalSieveWeight LognormalMellinIntegral
open scoped Classical

def value (A t : ℝ) : ℂ :=
  ∑' n : ℕ, (weight A ((n+1 : ℕ) : ℝ) : ℂ)*LogarithmicExponentialSum.function t ((n+1 : ℕ) : ℝ)

theorem kernel_norm (t y : ℝ) : ‖kernel t y‖=Real.exp (-y^2) := by
  rw [kernel,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),phase_norm,mul_one]

theorem kernel_integrable (t : ℝ) : Integrable (kernel t) := by
  have hc : Continuous (kernel t) := by
    have hGaussian : Continuous (fun y : ℝ ↦ (Real.exp (-y^2) : ℂ)) := by fun_prop
    exact hGaussian.mul (phase_continuous (-t))
  have hG : Integrable (fun y : ℝ ↦ Real.exp (-y^2)) := by
    simpa only [neg_one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  exact hG.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun y ↦ (kernel_norm t y).le))

theorem integrand_integrable (A t : ℝ) (hA : 0 < A) :
    IntegrableOn (fun x : ℝ ↦ (weight A x : ℂ)*LogarithmicExponentialSum.function t x) (Set.Ioi 0) := by
  have hShift : Integrable (fun y : ℝ ↦ kernel t (y-Real.log A)) := by
    simpa only [sub_eq_add_neg] using (kernel_integrable t).comp_add_right (-Real.log A)
  have hG := hShift.const_mul ((A : ℂ)*phase (-Real.log A) t)
  have hLog := (MeasureTheory.integrableOn_comp_log_Ioi_zero
    (fun y : ℝ ↦ (A : ℂ)*phase (-Real.log A) t*kernel t (y-Real.log A))).mpr hG
  apply hLog.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (integrand_identity A x t hA hx).symm

theorem summable_terms (A t : ℝ) (hA : 0 < A) :
    Summable (fun n : ℕ ↦ (weight A ((n+1 : ℕ) : ℝ) : ℂ)*
      LogarithmicExponentialSum.function t ((n+1 : ℕ) : ℝ)) := by
  have hNat : Summable (fun n : ℕ ↦ ((n : ℝ)^3)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by decide : 1 < (3 : ℕ))
  have hShift : Summable (fun n : ℕ ↦ 1/((n+1 : ℕ) : ℝ)^3) := by
    simpa only [one_div] using (summable_nat_add_iff 1).mpr hNat
  have hMajorant := hShift.mul_left (Real.exp 1*A^3)
  apply Summable.of_norm
  apply hMajorant.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A _),LogarithmicExponentialSum.function_norm,mul_one]
  exact (polynomial_tail_bound A _ hA (by exact_mod_cast (show 0 < n+1 by omega))).trans_eq (by ring)

theorem head_identity (A t : ℝ) (M : ℕ) :
    (∑ n ∈ Icc 1 M, (weight A n : ℂ)*LogarithmicExponentialSum.function t n)=
      ∑ i ∈ range M, (weight A ((i+1 : ℕ) : ℝ) : ℂ)*LogarithmicExponentialSum.function t ((i+1 : ℕ) : ℝ) := by
  rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range,show M+1-1=M by omega]
  simp only [Nat.add_comm]

theorem head_tendsto (A t : ℝ) (hA : 0 < A) :
    Tendsto (fun M : ℕ ↦ ∑ n ∈ Icc 1 M, (weight A n : ℂ)*LogarithmicExponentialSum.function t n)
      atTop (nhds (value A t)) := by
  have hh := (summable_terms A t hA).hasSum.tendsto_sum_nat
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun M ↦ (head_identity A t M).symm)
end PaperP1.LognormalSumIntegrability
