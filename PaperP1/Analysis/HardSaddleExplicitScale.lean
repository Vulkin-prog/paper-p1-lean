module

public import PaperP1.Analysis.SaddleScales

/-! # The explicit square-root form of the actual hard saddle

The square expansion is converted to an additive little-o at scale
nu=H/V. This is a consequence of the actual implicit root, with no
asymptotic shape supplied as a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardSaddleExplicitScale

open Set Filter PaperP1.SaddleParameters PaperP1.SaddleScales

def logCore (H : ℝ) : ℝ := Real.log H + Real.log (Real.log H) - Real.log 2 - 2

def explicitScale (H : ℝ) : ℝ := Real.sqrt (2 * H * logCore H)

theorem tendsto_logCore_atTop : Tendsto logCore atTop atTop := by
  change Tendsto (fun H : ℝ ↦ Real.log H + Real.log (Real.log H) - Real.log 2 - 2) atTop atTop
  have ht := Real.tendsto_log_atTop.atTop_add_atTop (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  simpa only [logCore, sub_eq_add_neg, Function.comp_def] using
    tendsto_atTop_add_const_right atTop (-2 : ℝ)
      (tendsto_atTop_add_const_right atTop (-Real.log 2) ht)

theorem finite_normalized_gap {H V : ℝ} (hH : 0 < H) (hV : 0 < V)
    (hcore : 0 ≤ logCore H) :
    |(2 * V - explicitScale H) / (H / V)| ≤ 2 * |V ^ 2 / H - logCore H / 2| := by
  have hG : 0 ≤ explicitScale H := Real.sqrt_nonneg _
  have hsq : explicitScale H ^ 2 = 2 * H * logCore H :=
    Real.sq_sqrt (by positivity)
  have hden : 0 < 2 * V + explicitScale H := by linarith
  have herror : V ^ 2 / H - logCore H / 2 =
      ((2 * V - explicitScale H) * (2 * V + explicitScale H)) / (4 * H) := by
    field_simp
    nlinarith only [hsq]
  have hid : (2 * V - explicitScale H) / (H / V) =
      (4 * V / (2 * V + explicitScale H)) * (V ^ 2 / H - logCore H / 2) := by
    rw [herror]
    field_simp
  have hcoef : 0 ≤ 4 * V / (2 * V + explicitScale H) := by positivity
  have hcoef2 : 4 * V / (2 * V + explicitScale H) ≤ 2 :=
    (div_le_iff₀ hden).mpr (by linarith only [hG])
  rw [hid, abs_mul, abs_of_nonneg hcoef]
  exact mul_le_mul_of_nonneg_right hcoef2 (abs_nonneg _)

theorem tendsto_hard_saddle_gap :
    Tendsto (fun H : ℝ ↦ (2 * saddleCutoff 1 H - explicitScale H) / saddleNu 1 H)
      atTop (nhds 0) := by
  have he : Tendsto (fun H : ℝ ↦ saddleCutoff 1 H ^ 2 / H - logCore H / 2)
      atTop (nhds 0) := by
    simpa only [logCore, one_div, one_mul, mul_comm (2⁻¹ : ℝ), div_eq_mul_inv] using
      PaperP1.SaddleExpansion.hard_saddle_second_order
  have hb : ∀ᶠ H : ℝ in atTop,
      |(2 * saddleCutoff 1 H - explicitScale H) / saddleNu 1 H| ≤
        2 * |saddleCutoff 1 H ^ 2 / H - logCore H / 2| := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (saddleThreshold 1),
      tendsto_logCore_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with H hH hroot hcore
    exact finite_normalized_gap hH (saddleCutoff_pos (by norm_num) hroot) hcore
  have hz := he.abs.const_mul 2
  apply squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hb)
  simpa only [abs_zero, mul_zero] using hz

theorem tendsto_hard_saddle_log_scale :
    Tendsto (fun X : ℝ ↦
      (2 * saddleCutoff 1 (Real.log X) - explicitScale (Real.log X)) / saddleNu 1 (Real.log X))
      atTop (nhds 0) := tendsto_hard_saddle_gap.comp Real.tendsto_log_atTop

end PaperP1.HardSaddleExplicitScale
