module

public import PaperP1.Analysis.HardSaddleReciprocalUpper
public import PaperP1.Asymptotics.ElementarySignedCostUpper
public import PaperP1.Asymptotics.CoarseSignedCostTheorem
public import PaperP1.Asymptotics.EnlargedRawValueProfile

/-! # The original signed forcing cost has hard-saddle order internally

The prime harmonic Euler bound and the internal raw profile give decay
exp(-V_N/10). The lower envelope is exp(-12V_N); the fine coefficient two remains open.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardSaddleSignedCostBounds

open Filter SaddleParameters SaddleScales HardSaddleGrowth SignedPrivateDyadicField
  SignedPrivateField SignedSaddleExcess SignedSaddleCostTheorem ReciprocalOddPivots

theorem uniform_upper_from_profile (C D : ℝ) (hD : 0 < D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      CriticalRawValueProfileUnderInputs.mass N (L + E + 1) ≤ (N : ℝ) ^ (19 / 12 : ℝ) →
      cost (data (E := E) (by omega : 2 ≤ N) hL) ≤ Real.exp (-saddleCutoff 1 (Real.log N) / 10) := by
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨NR, hr⟩ := HardSaddleReciprocalUpper.uniform_upper
  obtain ⟨NW, hw⟩ := SaddleLogPrefactors.logarithmic_width_le_height D
  obtain ⟨NF, hf⟩ := SaddleLogPrefactors.logarithmic_power (48 * K * D ^ 2) (by positivity) 2
    (1 / 90) (by norm_num)
  obtain ⟨NP, hp⟩ := CoarseSaddlePowerErrors.power_negligible 0 (-5 / 12) 1 (1 / (4 * K))
    (by norm_num) (by positivity)
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop HB))
  refine ⟨max NR (max NW (max NF (max NP NG))), ?_⟩
  intro N hN L E hL hcrit hwidth hprofile
  let t := saddleCutoff 1 (Real.log N)
  let V := saddleCutoff 1 (Real.log N)
  let B : ℝ := L + E + 2
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hH, hV, hsq, _hsq⟩ := hb (Real.log N) (hg N (by omega))
  have ht : 0 ≤ t := hV.le
  have htV : t ≤ V := le_rfl
  have hν : saddleNu 1 (Real.log N) ≤ t := by
    change Real.log N / V ≤ V
    exact (div_le_iff₀ hV).mpr (by nlinarith only [hsq])
  have hpref : 48 * K * D ^ 2 * Real.log N ^ 2 ≤ Real.exp (t / 90) := by
    have hh := hf N (by omega)
    exact hh.trans (Real.exp_le_exp.mpr (by nlinarith only [hν]))
  have hB : L + E + 2 ≤ N := by exact_mod_cast hwidth.trans (hw N (by omega))
  have hwidthB : B ≤ D * Real.log N := by simpa only [B, Nat.cast_add, Nat.cast_ofNat] using hwidth
  have hfinite := ElementarySignedCostUpper.profile_upper (by omega : 2 ≤ N) hL hB hcrit hprofile
  change cost (data (E := E) (by omega : 2 ≤ N) hL) ≤
    12 * K * B ^ 2 * (pivotSum (3 * N) + 1) / N + K * (N : ℝ) ^ (-5 / 12 : ℝ) at hfinite
  have hrec := hr N (by omega)
  have hmain : 12 * K * B ^ 2 * (pivotSum (3 * N) + 1) / N ≤
      (1 / 4 : ℝ) * Real.exp (-t / 10) := by
    calc
      _ ≤ 12 * K * B ^ 2 * ((N : ℝ) * Real.exp (-t / 9)) / N := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrec (by positivity)) hn.le
      _ = 12 * K * B ^ 2 * Real.exp (-t / 9) := by field_simp
      _ ≤ 12 * K * (D * Real.log N) ^ 2 * Real.exp (-t / 9) := by gcongr
      _ = (12 * K * D ^ 2 * Real.log N ^ 2) * Real.exp (-t / 9) := by ring
      _ ≤ (Real.exp (t / 90) / 4) * Real.exp (-t / 9) :=
        mul_le_mul_of_nonneg_right (by linarith only [hpref]) (Real.exp_nonneg _)
      _ = (1 / 4 : ℝ) * (Real.exp (t / 90) * Real.exp (-t / 9)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hraw : K * (N : ℝ) ^ (-5 / 12 : ℝ) ≤ (1 / 4 : ℝ) * Real.exp (-t / 10) := by
    have hh := hp N (by omega)
    simp only [Real.rpow_zero, mul_one, one_mul, neg_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hK.le
    have hid : K * (1 / (4 * K) * Real.exp (-V)) = (1 / 4 : ℝ) * Real.exp (-V) := by field_simp
    change K * (N : ℝ) ^ (-5 / 12 : ℝ) ≤ K * (1 / (4 * K) * Real.exp (-V)) at hmul
    rw [hid] at hmul
    exact hmul.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [htV, ht])) (by norm_num))
  nlinarith only [hfinite, hmain, hraw, Real.exp_pos (-t / 10)]

theorem uniform_upper (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        specifiedCost N L ≤ Real.exp (-saddleCutoff 1 (Real.log N) / 10) := by
  obtain ⟨NP, hp⟩ := EnlargedRawValueProfile.uniform_profile C (1 / 12) (by norm_num)
  obtain ⟨NW, hw⟩ := uniform_width C
  obtain ⟨NU, hu⟩ := uniform_upper_from_profile C widthConstant widthConstant_pos
  refine ⟨max NP (max NW NU), ?_⟩
  intro N hN L hL hcrit
  rw [specifiedCost_eq (by omega : 2 ≤ N) hL]
  apply hu N (by omega) L (excess N) hL hcrit (hw N (by omega) L hcrit)
  simpa only [CriticalRawValueProfile.mass, CriticalRawValueProfileUnderInputs.mass,
    show (3 : ℝ) / 2 + 1 / 12 = 19 / 12 by norm_num] using hp N (by omega) L hcrit

theorem uniform_sandwich (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Real.exp (-12 * saddleCutoff 1 (Real.log N)) ≤ specifiedCost N L ∧
          specifiedCost N L ≤ Real.exp (-saddleCutoff 1 (Real.log N) / 10) := by
  obtain ⟨NL, hl⟩ := CoarseSignedCostTheorem.uniform_lower C
  obtain ⟨NU, hu⟩ := uniform_upper C
  exact ⟨max NL NU, fun N hN L hL hcrit ↦
    ⟨hl N (by omega) L hL hcrit, hu N (by omega) L hL hcrit⟩⟩

theorem uniform_log_sandwich (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        -12 * saddleCutoff 1 (Real.log N) ≤ Real.log (specifiedCost N L) ∧
          Real.log (specifiedCost N L) ≤ -saddleCutoff 1 (Real.log N) / 10 := by
  obtain ⟨N₀, h⟩ := uniform_sandwich C
  refine ⟨N₀, ?_⟩
  intro N hN L hL hcrit
  obtain ⟨hl, hu⟩ := h N hN L hL hcrit
  have hcpos : 0 < specifiedCost N L := (Real.exp_pos _).trans_le hl
  have hlow := Real.log_le_log (Real.exp_pos _) hl
  have hhigh := Real.log_le_log hcpos hu
  exact ⟨by simpa only [Real.log_exp] using hlow, by simpa only [Real.log_exp] using hhigh⟩

theorem uniform_normalized_bounds (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (1 / 10 : ℝ) ≤ -Real.log (specifiedCost N L) / saddleCutoff 1 (Real.log N) ∧
          -Real.log (specifiedCost N L) / saddleCutoff 1 (Real.log N) ≤ 12 := by
  obtain ⟨NC, hc⟩ := uniform_log_sandwich C
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop HB))
  refine ⟨max NC NG, ?_⟩
  intro N hN L hL hcrit
  have hV := (hb (Real.log N) (hg N (by omega))).2.1
  obtain ⟨hl, hu⟩ := hc N (by omega) L hL hcrit
  exact ⟨(le_div_iff₀ hV).mpr (by linarith only [hu]),
    (div_le_iff₀ hV).mpr (by linarith only [hl])⟩

end PaperP1.HardSaddleSignedCostBounds
