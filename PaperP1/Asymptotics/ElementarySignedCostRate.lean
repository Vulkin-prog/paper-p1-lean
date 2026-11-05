module

public import PaperP1.Asymptotics.ElementarySignedCostUpper
public import PaperP1.Asymptotics.ElementarySignedPowerObstruction
public import PaperP1.Asymptotics.EnlargedRawValueProfile

/-! # The specified signed forcing has a strictly subpolynomial decay rate internally

Its cost tends to zero faster than every fixed inverse logarithmic power,
but it has no polynomial decay. The fine saddle equivalent remains separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementarySignedCostRate

open Filter SignedPrivateDyadicField SignedSaddleExcess SignedSaddleCostTheorem

theorem uniform_logarithmic_upper (C : ℝ) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Real.log N ^ A * specifiedCost N L ≤ 1 := by
  obtain ⟨NP, hp⟩ := EnlargedRawValueProfile.uniform_profile C (1 / 12) (by norm_num)
  obtain ⟨NW, hw⟩ := uniform_width C
  obtain ⟨NU, hu⟩ := ElementarySignedCostUpper.uniform_upper_from_profile C widthConstant widthConstant_pos A
  refine ⟨max NP (max NW NU), ?_⟩
  intro N hN L hL hcrit
  rw [specifiedCost_eq (by omega : 2 ≤ N) hL]
  apply hu N (by omega) L (excess N) hL hcrit (hw N (by omega) L hcrit)
  simpa only [CriticalRawValueProfile.mass, CriticalRawValueProfileUnderInputs.mass,
    show (3 : ℝ) / 2 + 1 / 12 = 19 / 12 by norm_num] using hp N (by omega) L hcrit

theorem uniform_log_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |Real.log (specifiedCost N L)| ≤ ε * Real.log N := by
  obtain ⟨NL, hl⟩ := ElementarySignedPowerObstruction.uniform_power_obstruction C ε 1 hε
  obtain ⟨NU, hu⟩ := uniform_logarithmic_upper C 0
  refine ⟨max NL NU, ?_⟩
  intro N hN L hL hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlower := hl N (by omega) L hL hcrit
  simp only [one_mul] at hlower
  have hupper := hu N (by omega) L hL hcrit
  simp only [pow_zero, one_mul] at hupper
  have hcpos : 0 < specifiedCost N L := (Real.rpow_pos_of_pos hn (-ε)).trans_le hlower
  have hloglow := Real.log_le_log (Real.rpow_pos_of_pos hn (-ε)) hlower
  rw [Real.log_rpow hn] at hloglow
  have hloghigh : Real.log (specifiedCost N L) ≤ 0 := Real.log_nonpos hcpos.le hupper
  rw [abs_of_nonpos hloghigh]
  linarith only [hloglow]

theorem normalized_log_limit (C : ℝ) (length : ℕ → ℕ)
    (hseq : ∀ᶠ N : ℕ in atTop, 1 ≤ length N ∧
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Tendsto (fun N : ℕ ↦ Real.log (specifiedCost N (length N)) / Real.log N) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨NL, hl⟩ := uniform_log_bound C (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := eventually_atTop.mp hseq
  refine ⟨max NL (max NS 2), ?_⟩
  intro N hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := hl N (by omega) (length N) (hs N (by omega)).1 (hs N (by omega)).2
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog]
  exact ((div_le_iff₀ hlog).mpr hh).trans_lt (by linarith only [hε])

theorem weighted_cost_tendsto_zero (C : ℝ) (A : ℕ) (length : ℕ → ℕ)
    (hseq : ∀ᶠ N : ℕ in atTop, 1 ≤ length N ∧
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Tendsto (fun N : ℕ ↦ Real.log N ^ A * specifiedCost N (length N)) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨NU, hu⟩ := uniform_logarithmic_upper C (A + 1)
  obtain ⟨NL, hl⟩ := ElementarySignedPowerObstruction.uniform_power_obstruction C 1 1 (by norm_num)
  obtain ⟨NS, hs⟩ := eventually_atTop.mp hseq
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop (2 / ε)))
  refine ⟨max NU (max NL (max NS (max NG 2))), ?_⟩
  intro N hN
  obtain ⟨hL, hcrit⟩ := hs N (by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlow := hl N (by omega) (length N) hL hcrit
  simp only [one_mul] at hlow
  have hcpos : 0 < specifiedCost N (length N) := (Real.rpow_pos_of_pos hn (-1)).trans_le hlow
  have hupper := hu N (by omega) (length N) hL hcrit
  have hcost : Real.log N ^ A * specifiedCost N (length N) ≤ 1 / Real.log N := by
    apply (le_div_iff₀ hlog).mpr
    rw [pow_succ] at hupper
    nlinarith only [hupper]
  have hlogbound := (div_le_iff₀ hε).mp (hg N (by omega))
  have hrec : 1 / Real.log N ≤ ε / 2 := (div_le_iff₀ hlog).mpr (by nlinarith only [hlogbound])
  rw [Real.dist_eq, sub_zero, abs_of_pos (mul_pos (pow_pos hlog A) hcpos)]
  exact (hcost.trans hrec).trans_lt (by linarith only [hε])

theorem cost_tendsto_zero (C : ℝ) (length : ℕ → ℕ)
    (hseq : ∀ᶠ N : ℕ in atTop, 1 ≤ length N ∧
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Tendsto (fun N : ℕ ↦ specifiedCost N (length N)) atTop (nhds 0) := by
  simpa only [pow_zero, one_mul] using weighted_cost_tendsto_zero C 0 length hseq

end PaperP1.ElementarySignedCostRate
