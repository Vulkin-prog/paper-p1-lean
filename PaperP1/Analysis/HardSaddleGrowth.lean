module

public import PaperP1.Analysis.HardSaddleExplicitScale

/-! # Growth comparisons for the actual hard saddle

The eventual square bounds, positivity and sublinear growth are deduced
from the already proved actual-root limits. No prime-sum input is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardSaddleGrowth

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.SaddleAsymptotics
  PaperP1.HardSaddleExplicitScale

theorem tendsto_cutoff_atTop : Tendsto (saddleCutoff 1) atTop atTop := by
  have ht := PaperP1.ExponentialIntegral.tendsto_saddleCostParam_atTop.comp
    (tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ) < 1))
  change Tendsto (fun H : ℝ ↦ 1 * PaperP1.ExponentialIntegral.saddleCostParam (saddleParameter 1 H)) atTop atTop
  simpa only [one_mul, Function.comp_def] using ht

theorem tendsto_cutoff_div_height :
    Tendsto (fun H : ℝ ↦ saddleCutoff 1 H / H) atTop (nhds 0) := by
  have ht := (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).inv_tendsto_atTop
  change Tendsto (fun H : ℝ ↦ (saddleNu 1 H)⁻¹) atTop (nhds 0) at ht
  simpa only [saddleNu, inv_div] using ht

theorem square_band_eventually : ∃ H₀ : ℝ, ∀ H ≥ H₀,
    0 < H ∧ 0 < saddleCutoff 1 H ∧ H ≤ saddleCutoff 1 H ^ 2 ∧
      saddleCutoff 1 H ^ 2 ≤ H * Real.log H := by
  have ht := tendsto_saddleCutoff_square_normalized (by norm_num : (0 : ℝ) < 1)
  have hl := ht.eventually (eventually_gt_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))
  have hu := ht.eventually (eventually_lt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  apply eventually_atTop.mp
  filter_upwards [hl, hu, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_ge_atTop (saddleThreshold 1)] with H hl hu hH hlog hroot
  have hd : 0 < H * Real.log H := mul_pos hH (by linarith)
  have hlo := (le_div_iff₀ hd).mp hl.le
  have hhi := (div_le_iff₀ hd).mp hu.le
  refine ⟨hH, saddleCutoff_pos (by norm_num) hroot, ?_, ?_⟩
  · nlinarith only [hlo, mul_nonneg hH.le (by linarith : 0 ≤ Real.log H - 4)]
  · simpa only [one_mul] using hhi

theorem tendsto_log_div_cutoff :
    Tendsto (fun H : ℝ ↦ Real.log H / saddleCutoff 1 H) atTop (nhds 0) := by
  obtain ⟨H₀, hband⟩ := square_band_eventually
  have hle : ∀ᶠ H : ℝ in atTop,
      0 ≤ Real.log H / saddleCutoff 1 H ∧
      Real.log H / saddleCutoff 1 H ≤ Real.log H / saddleNu 1 H := by
    filter_upwards [eventually_ge_atTop H₀, eventually_ge_atTop (1 : ℝ)] with H hH hH1
    obtain ⟨hpos, hv, hlo, _hhi⟩ := hband H hH
    have hn : 0 < saddleNu 1 H := div_pos hpos hv
    have hnV : saddleNu 1 H ≤ saddleCutoff 1 H := (div_le_iff₀ hv).mpr (by nlinarith only [hlo])
    exact ⟨div_nonneg (Real.log_nonneg hH1) hv.le,
      div_le_div_of_nonneg_left (Real.log_nonneg hH1) hn hnV⟩
  exact squeeze_zero' (hle.mono fun _ h ↦ h.1) (hle.mono fun _ h ↦ h.2)
    (tendsto_log_div_saddleNu (by norm_num : (0 : ℝ) < 1))

theorem scale_upper_eventually : ∃ H₀ : ℝ, ∀ H ≥ H₀,
    explicitScale H ≤ 3 * saddleCutoff 1 H := by
  obtain ⟨HB, hB⟩ := square_band_eventually
  have he : Tendsto (fun H : ℝ ↦ saddleCutoff 1 H ^ 2 / H - logCore H / 2)
      atTop (nhds 0) := by
    simpa only [logCore, one_div, one_mul, mul_comm (2⁻¹ : ℝ), div_eq_mul_inv] using
      PaperP1.SaddleExpansion.hard_saddle_second_order
  have hevent := he.eventually (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop HB, hevent,
    tendsto_logCore_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with H hH herr hcore
  obtain ⟨hpos, hv, hlo, _hhi⟩ := hB H hH
  have hq : logCore H ≤ 4 * saddleCutoff 1 H ^ 2 / H := by
    have hh : 1 ≤ saddleCutoff 1 H ^ 2 / H := (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using hlo)
    calc
      logCore H ≤ 4 * (saddleCutoff 1 H ^ 2 / H) := by linarith only [herr, hh]
      _ = _ := by ring
  have hqm := (le_div_iff₀ hpos).mp hq
  have hsq : explicitScale H ^ 2 = 2 * H * logCore H := Real.sq_sqrt (by positivity)
  have hg : 0 ≤ explicitScale H := Real.sqrt_nonneg _
  nlinarith only [hqm, hsq, hg, hv]

end PaperP1.HardSaddleGrowth
