module

public import PaperP1.Asymptotics.SignedDyadicCostUpper
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Analysis.SaddleLogPrefactors
public import PaperP1.Analysis.ReciprocalOddPivotTripleScale

/-! # Sharp saddle upper cost from the actual finite ledger and a smaller raw profile power -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSaddleCostUpper

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.OrdinaryReciprocalPrimeInput
  PaperP1.SignedPrivateDyadicField PaperP1.SignedPrivateField PaperP1.ReciprocalOddPivots

theorem uniform_upper_from_profile (hinput : EIPInput) (C D : ℝ) (hD : 0 < D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      CriticalRawValueProfileUnderInputs.mass N (L + E + 1) ≤ (N : ℝ) ^ (19 / 12 : ℝ) →
      cost (data (E := E) (by omega : 2 ≤ N) hL) ≤
        Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨NR, hR⟩ := ReciprocalOddPivotTripleScale.upper_with_one hinput (ε / 4) (by positivity)
  obtain ⟨NW, hW⟩ := SaddleLogPrefactors.logarithmic_width_le_height D
  obtain ⟨NK, hPref⟩ := SaddleLogPrefactors.logarithmic_power (192 * K * D ^ 2)
    (by positivity) 2 (ε / 2) (by positivity)
  obtain ⟨NP, hP⟩ := SaddlePowerErrors.power_negligible 0 (-5 / 12) 0 (1 / (4 * K))
    (by norm_num) (by positivity)
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hG⟩ := eventually_atTop.mp
    (hnlog.eventually (eventually_ge_atTop (max (saddleThreshold 1) 1)))
  refine ⟨max NR (max NW (max NK (max NP NG))), ?_⟩
  intro N hN L E hL hcrit hwidth hprofile
  let B : ℝ := ((L + E + 2 : ℕ) : ℝ)
  let V := saddleCutoff 1 (Real.log N)
  let ν := saddleNu 1 (Real.log N)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdom := hG N (by omega)
  have hH : 0 < Real.log N := by have := (le_max_right _ _).trans hdom; linarith
  have hV : 0 < V := saddleCutoff_pos (by norm_num) (by order)
  have hnu : 0 ≤ ν := (div_pos hH hV).le
  have hεnu : 0 ≤ ε * ν := mul_nonneg hε.le hnu
  have hB : L + E + 2 ≤ N := by exact_mod_cast hwidth.trans (hW N (by omega))
  have hfinite := SignedDyadicCostUpper.finite_upper_coarse (by omega : 2 ≤ N) hL hB
  have hnom : ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ K * (N : ℝ) ^ (-2 : ℝ) :=
    CriticalChannelPowers.nominal_square_upper (by omega) hcrit
  have hrec := hR N (by omega)
  have hpre := hPref N (by omega)
  have hpow := hP N (by omega)
  simp only [Real.rpow_zero, mul_one, zero_mul, sub_zero] at hpow
  have hbound : cost (data (E := E) (by omega : 2 ≤ N) hL) ≤
      48 * K * B ^ 2 * Real.exp (-2 * V + (ε / 4) * ν) + K * (N : ℝ) ^ (-5 / 12 : ℝ) := by
    calc
      _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 *
          (12 * (N : ℝ) * B ^ 2 * (pivotSum (3 * N) + 1) + (N : ℝ) ^ (19 / 12 : ℝ)) := by
        have hh := mul_le_mul_of_nonneg_left
          (add_le_add_left hprofile (12 * (N : ℝ) * B ^ 2 * (pivotSum (3 * N) + 1)))
          (sq_nonneg ((2 ^ L : ℝ)⁻¹))
        exact hfinite.trans (by simpa only [B, Nat.cast_add, Nat.cast_ofNat, add_comm] using hh)
      _ ≤ (K * (N : ℝ) ^ (-2 : ℝ)) *
          (12 * (N : ℝ) * B ^ 2 * (pivotSum (3 * N) + 1) + (N : ℝ) ^ (19 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_right hnom (by
          exact add_nonneg (mul_nonneg (by positivity) (by linarith only [pivotSum_nonneg (3 * N)]))
            (Real.rpow_nonneg hn.le _))
      _ ≤ (K * (N : ℝ) ^ (-2 : ℝ)) *
          (12 * (N : ℝ) * B ^ 2 * (4 * N * Real.exp (-2 * V + (ε / 4) * ν)) + (N : ℝ) ^ (19 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (by
            have hh := add_le_add_right
              (mul_le_mul_of_nonneg_left hrec (by positivity : (0 : ℝ) ≤ 12 * (N : ℝ) * B ^ 2))
              ((N : ℝ) ^ (19 / 12 : ℝ))
            simpa only [V, ν, add_comm] using hh)
          (by positivity)
      _ = _ := by
        rw [mul_add]
        congr 1
        · rw [Real.rpow_neg hn.le, Real.rpow_two]
          field_simp
          ring
        · rw [mul_assoc, ← Real.rpow_add hn]
          norm_num
  have hBs : B ^ 2 ≤ (D * Real.log N) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg (L + E + 2)) hwidth 2
  have hgeom : 48 * K * B ^ 2 ≤ Real.exp ((ε / 2) * ν) / 4 := by
    have hh := mul_le_mul_of_nonneg_left hBs (by positivity : (0 : ℝ) ≤ 48 * K)
    nlinarith only [hh, hpre]
  have hgeoterm : 48 * K * B ^ 2 * Real.exp (-2 * V + (ε / 4) * ν) ≤
      (1 / 4 : ℝ) * Real.exp (-2 * V + ε * ν) := by
    calc
      _ ≤ (Real.exp ((ε / 2) * ν) / 4) * Real.exp (-2 * V + (ε / 4) * ν) :=
        mul_le_mul_of_nonneg_right hgeom (Real.exp_pos _).le
      _ = (1 / 4 : ℝ) * Real.exp (-2 * V + (3 * ε / 4) * ν) := by
        rw [show -2 * V + (3 * ε / 4) * ν = (ε / 2) * ν + (-2 * V + (ε / 4) * ν) by ring,
          Real.exp_add ((ε / 2) * ν) (-2 * V + (ε / 4) * ν)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hεnu])) (by norm_num)
  have hraw : K * (N : ℝ) ^ (-5 / 12 : ℝ) ≤ (1 / 4 : ℝ) * Real.exp (-2 * V) := by
    have hh := mul_le_mul_of_nonneg_left hpow hK.le
    calc
      _ ≤ K * (1 / (4 * K) * Real.exp (-2 * V)) := hh
      _ = _ := by field_simp
  have hrawterm : K * (N : ℝ) ^ (-5 / 12 : ℝ) ≤
      (1 / 4 : ℝ) * Real.exp (-2 * V + ε * ν) :=
    hraw.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hεnu])) (by norm_num))
  nlinarith only [hbound, hgeoterm, hrawterm, Real.exp_pos (-2 * V + ε * ν)]

end PaperP1.SignedSaddleCostUpper
