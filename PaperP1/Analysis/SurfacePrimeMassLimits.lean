module

public import PaperP1.Arithmetic.SurfaceDeterminantPrimeWindow
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The actual retained-prime mass has unit leading logarithmic coefficient for every fixed lower cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SurfacePrimeMassLimits

open Filter Topology SurfaceDeterminantPrimeWindow

theorem mass_ratio (K : ℕ) :
    Tendsto (fun e : ℕ ↦ mass K e / Real.log (e : ℝ)) atTop (𝓝 1) := by
  have hi : Tendsto (fun e : ℕ ↦ (Real.log (e : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlo : Tendsto (fun e : ℕ ↦ 1 - cost K / Real.log (e : ℝ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub (hi.const_mul (cost K))
  have hhi : Tendsto (fun e : ℕ ↦ 1 + (Real.log 4 + 4) / Real.log (e : ℝ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add (hi.const_mul (Real.log 4 + 4))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop K, eventually_ge_atTop 2] with e hK he
    have hlog : 0 < Real.log (e : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < e by omega))
    have hh := (div_le_div_iff_of_pos_right hlog).mpr (mass_lower_bound K e (by omega) hK)
    simpa only [sub_div, div_self hlog.ne'] using hh
  · filter_upwards [eventually_ge_atTop 2] with e he
    have hlog : 0 < Real.log (e : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < e by omega))
    have hh := (div_le_div_iff_of_pos_right hlog).mpr (mass_upper_bound K e (by omega))
    simpa only [add_div, div_self hlog.ne'] using hh

end PaperP1.SurfacePrimeMassLimits
