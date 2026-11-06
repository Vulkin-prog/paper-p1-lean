module

public import PaperP1.Analysis.SmoothLongMeanStability


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothLongLengthGeometry
open Finset Nat Filter PaperP1 SmoothLongMeanStability
open scoped Classical

theorem length_sqrt_lower (N : ℕ) (hN : 2 ≤ N) : Real.sqrt (N : ℝ) ≤ (length N : ℝ) := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hSqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hLog
  have hLogN : Real.log (N : ℝ) ≤ (N : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos hNP
    linarith only [hh]
  have hRoot : Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hLogN
  calc
    _ ≤ (N : ℝ)/Real.sqrt (Real.log (N : ℝ)) := by
      apply (le_div_iff₀ hSqrt).mpr
      calc
        _ ≤ Real.sqrt (N : ℝ)*Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left hRoot (Real.sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt hNP.le
    _ ≤ _ := length_lower N

theorem length_grows : Tendsto (fun N : ℕ ↦ (length N : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    ((eventually_ge_atTop 2).mono (fun N hN ↦ length_sqrt_lower N hN))
  exact Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem relative_size_bound (N : ℕ) (hN : 2 ≤ N) :
    (length N : ℝ)/(N : ℝ) ≤ 1/Real.sqrt (Real.log (N : ℝ))+1/(N : ℝ) := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hSqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr (Real.log_pos hNR)
  calc
    _ ≤ ((N : ℝ)/Real.sqrt (Real.log (N : ℝ))+1)/(N : ℝ) :=
      div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hNP.le
    _ = _ := by field_simp

theorem relative_size_tendsto : Tendsto (fun N : ℕ ↦ (length N : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hLog := Real.tendsto_log_atTop.comp hNat
  have hSqrt := Real.tendsto_sqrt_atTop.comp hLog
  have hLimit : Tendsto (fun N : ℕ ↦ 1/Real.sqrt (Real.log (N : ℝ))+1/(N : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_apply,one_div,zero_add] using
      (tendsto_inv_atTop_zero.comp hSqrt).add (tendsto_inv_atTop_zero.comp hNat)
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity))
    ((eventually_ge_atTop 2).mono (fun N hN ↦ relative_size_bound N hN)) hLimit

end PaperP1.SmoothLongLengthGeometry
