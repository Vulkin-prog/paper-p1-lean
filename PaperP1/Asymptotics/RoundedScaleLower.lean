module

public import PaperP1.Asymptotics.DoubledDeterminantScale
public import PaperP1.Asymptotics.DeterminantNormalizedWeights

/-! # The actual rounded determinant scale eventually exceeds every fixed grid threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RoundedScaleLower

open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale

theorem shape_nonnegative {N : ℕ} (hN : 2 ≤ N) {D E U V : ℝ}
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hU : 1 ≤ U) (hV : 1 ≤ V) : 0 ≤ logShape N D E U V := by
  have hDE : 1 ≤ D * E := by nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hE)]
  have hUV : 1 ≤ U * V := by nlinarith [mul_nonneg (sub_nonneg.mpr hU) (sub_nonneg.mpr hV)]
  have hlogDE := Real.log_nonneg hDE
  have hlogUV := Real.log_nonneg hUV
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  unfold logShape
  positivity

theorem uniform_lower (L : ℕ) (hL : 1 ≤ L) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D E U V : ℝ, 1 ≤ D → 1 ≤ E → 1 ≤ U → 1 ≤ V →
      L ≤ horizontalScale N D E U V ζ := by
  obtain ⟨N₀, hlog⟩ := DeterminantNormalizedWeights.fixed_log_error L ζ hζ
  refine ⟨N₀, ?_⟩
  intro N hN D E U V hD hE hU hV
  obtain ⟨hN₂, herr⟩ := hlog N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hln : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpow : (L : ℝ) ≤ (N : ℝ) ^ ζ := by
    have he := Real.exp_le_exp.mpr ((div_le_iff₀ hln).mp herr)
    rw [Real.exp_log hLp] at he
    simpa only [Real.rpow_def_of_pos hn, mul_comm] using he
  have hexp : 1 ≤ Real.exp (logShape N D E U V) := by
    have hh := Real.exp_le_exp.mpr (shape_nonnegative hN₂ hD hE hU hV)
    simpa only [Real.exp_zero] using hh
  have hscale := horizontalScale_lower N D E U V ζ
  have hm : (L : ℝ) ≤ horizontalScale N D E U V ζ := by
    calc
      _ ≤ (N : ℝ) ^ ζ := hpow
      _ ≤ (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hn.le ζ)
      _ ≤ _ := hscale
  exact_mod_cast hm

end PaperP1.RoundedScaleLower
