module

public import PaperP1.Analysis.SaddleScales

/-! # Monotonicity of the actual saddle parameter and both derived scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaddleMonotonicity

open PaperP1.SaddleBranch PaperP1.SaddleParameters PaperP1.SaddleScales
  PaperP1.ExponentialIntegral

theorem parameter_monotone {a t H : ℝ} (ha : 0 < a) (ht : saddleThreshold a ≤ t)
    (htH : t ≤ H) : saddleParameter a t ≤ saddleParameter a H := by
  have hH := ht.trans htH
  obtain ⟨hpt, het⟩ := saddleParameter_spec ha ht
  obtain ⟨hpH, heH⟩ := saddleParameter_spec ha hH
  apply ((strictMonoOn_saddleHeight ha).le_iff_le hpt hpH).mp
  rwa [het, heH]

theorem cutoff_monotone {a t H : ℝ} (ha : 0 < a) (ht : saddleThreshold a ≤ t)
    (htH : t ≤ H) : saddleCutoff a t ≤ saddleCutoff a H := by
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  have hpt : 1 ≤ saddleParameter a t := hb.trans (saddleParameter_spec ha ht).1
  have hpH : 1 ≤ saddleParameter a H := hb.trans (saddleParameter_spec ha (ht.trans htH)).1
  exact mul_le_mul_of_nonneg_left
    (strictMonoOn_saddleCostParam.monotoneOn hpt hpH (parameter_monotone ha ht htH)) ha.le

theorem nu_monotone {a t H : ℝ} (ha : 0 < a) (ht : saddleThreshold a ≤ t)
    (htH : t ≤ H) : saddleNu a t ≤ saddleNu a H := by
  unfold saddleNu
  rw [div_saddleCutoff_eq_ratio ha ht, div_saddleCutoff_eq_ratio ha (ht.trans htH)]
  have hb : 1 ≤ saddleParameterBase := by linarith [saddleParameterBase_ge_two]
  exact strictMonoOn_saddleRatio.monotoneOn
    (hb.trans (saddleParameter_spec ha ht).1)
    (hb.trans (saddleParameter_spec ha (ht.trans htH)).1) (parameter_monotone ha ht htH)

end PaperP1.SaddleMonotonicity
