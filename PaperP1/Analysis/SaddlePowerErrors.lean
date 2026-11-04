module

public import PaperP1.Analysis.DyadicReciprocalScaleBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Every fixed smaller power is negligible at the actual reciprocal saddle -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaddlePowerErrors

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.HardSaddleGrowth
  PaperP1.DyadicReciprocalScaleBounds

theorem power_negligible (d β ε η : ℝ) (hβ : β < d) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      (N : ℝ) ^ β ≤ η * (N : ℝ) ^ d *
        Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) := by
  have ht : Tendsto (fun H : ℝ ↦
      (2 * saddleCutoff 1 H + ε * saddleNu 1 H - Real.log η) / H) atTop (nhds 0) := by
    have hc : Tendsto (fun H : ℝ ↦ Real.log η / H) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    have hh := ((tendsto_cutoff_div_height.const_mul 2).add (tendsto_nu_div_height.const_mul ε)).sub hc
    simpa only [add_div, sub_div, mul_div_assoc, mul_zero, add_zero, sub_zero] using hh
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((hnlog.eventually (eventually_gt_atTop (0 : ℝ))).and
      ((ht.comp hnlog).eventually (eventually_lt_nhds (sub_pos.mpr hβ))))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hH, he⟩ := h N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  change (2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N) - Real.log η) / Real.log N < d - β at he
  have he' := (div_le_iff₀ hH).mp he.le
  have hexponent : Real.log N * β ≤ Real.log η +
      (Real.log N * d + (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N))) := by
    nlinarith only [he']
  have hh := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_add (Real.log η), Real.exp_log hη,
    Real.exp_add (Real.log N * d)] at hh
  simpa only [Real.rpow_def_of_pos hn, mul_assoc] using hh

end PaperP1.SaddlePowerErrors
