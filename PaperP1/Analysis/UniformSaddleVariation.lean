module

public import PaperP1.Analysis.ExplicitSaddleVariation
public import PaperP1.Analysis.HardSaddleGrowth

/-! # Uniform explicit-saddle stability on the small square-part range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformSaddleVariation

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.HardSaddleExplicitScale
  PaperP1.HardSaddleGrowth PaperP1.ExplicitSaddleVariation

theorem uniform_left_variation (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ t : ℝ,
      H - A * saddleCutoff 1 H ≤ t → t ≤ H →
      |explicitScale H - explicitScale t| ≤ ε * saddleNu 1 H := by
  obtain ⟨TB, hB⟩ := square_band_eventually
  obtain ⟨TG, hG⟩ := scale_upper_eventually
  obtain ⟨TC, hC⟩ := eventually_atTop.mp
    (tendsto_logCore_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨TL, hL⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  have hhalf : Tendsto (fun H : ℝ ↦ A * saddleCutoff 1 H / H) atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero] using tendsto_cutoff_div_height.const_mul A
  obtain ⟨TH, hH⟩ := eventually_atTop.mp
    (hhalf.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hsmall : Tendsto (fun H : ℝ ↦ (9 * A) * (Real.log H / saddleNu 1 H)) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_log_div_saddleNu (by norm_num : (0 : ℝ) < 1)).const_mul (9 * A)
  obtain ⟨TE, hE⟩ := eventually_atTop.mp (hsmall.eventually (eventually_lt_nhds hε))
  let T : ℝ := max 1 (max TC TL)
  refine ⟨max (2 * T) (max TB (max TG (max TH TE))), ?_⟩
  intro H hH₀ t htlo hthi
  obtain ⟨hp, hv, _hvlo, hvhi⟩ := hB H (by dsimp [T] at *; order)
  have hHt : 2 * T ≤ H := (le_max_left _ _).trans hH₀
  have hh := (div_le_iff₀ hp).mp (hH H (by order)).le
  have htT : T ≤ t := by linarith only [htlo, hHt, hh]
  have ht : 0 < t := lt_of_lt_of_le (by dsimp [T]; positivity) htT
  have htlog : 1 ≤ Real.log t := hL t (by dsimp [T] at *; order)
  have htcore : 0 ≤ logCore t := (by norm_num : (0 : ℝ) ≤ 1).trans (hC t (by dsimp [T] at *; order))
  have hHcore : 1 ≤ logCore H := hC H (by dsimp [T] at *; order)
  obtain ⟨hd0, hd⟩ := finite_scale_difference ht htlog hthi htcore hHcore
  have hg := hG H (by order)
  have hdiff : H - t ≤ A * saddleCutoff 1 H := by linarith only [htlo]
  have hprod : 3 * (H - t) * explicitScale H ≤ 9 * A * saddleCutoff 1 H ^ 2 := by
    have hm := mul_le_mul hdiff hg (Real.sqrt_nonneg (2 * H * logCore H))
      (mul_nonneg hA hv.le)
    nlinarith only [hm]
  have hbig : explicitScale H - explicitScale t ≤ 9 * A * Real.log H := by
    calc
      _ ≤ 3 * (H - t) * explicitScale H / H := hd
      _ ≤ (9 * A * saddleCutoff 1 H ^ 2) / H := div_le_div_of_nonneg_right hprod hp.le
      _ ≤ (9 * A * (H * Real.log H)) / H :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvhi (by positivity)) hp.le
      _ = _ := by field_simp
  have hn : 0 < saddleNu 1 H := div_pos hp hv
  have he := (hE H (by order)).le
  have he' : 9 * A * Real.log H ≤ ε * saddleNu 1 H := by
    apply (div_le_iff₀ hn).mp
    simpa only [mul_div_assoc] using he
  rw [abs_of_nonneg hd0]
  exact hbig.trans he'

end PaperP1.UniformSaddleVariation
