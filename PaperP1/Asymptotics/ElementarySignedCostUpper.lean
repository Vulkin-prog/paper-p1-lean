module

public import PaperP1.Asymptotics.SignedDyadicCostUpper
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Analysis.SaddleLogPrefactors
public import PaperP1.Analysis.ElementaryReciprocalPivotUpper

/-! # Every fixed logarithmic power bounds the signed cost from above internally -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementarySignedCostUpper

open Filter SignedPrivateDyadicField SignedPrivateField ReciprocalOddPivots

theorem profile_upper {N L E : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (hB : L + E + 2 ≤ N) (hcrit : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (hprofile : CriticalRawValueProfileUnderInputs.mass N (L + E + 1) ≤ (N : ℝ) ^ (19 / 12 : ℝ)) :
    cost (data (E := E) hN hL) ≤
      12 * ((2 : ℝ) ^ C) ^ 2 * (L + E + 2 : ℝ) ^ 2 * (pivotSum (3 * N) + 1) / N +
        ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-5 / 12 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfinite := SignedDyadicCostUpper.finite_upper_coarse hN hL hB
  have hnom := CriticalChannelPowers.nominal_square_upper hN hcrit
  calc
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 *
        (12 * (N : ℝ) * (L + E + 2 : ℝ) ^ 2 * (pivotSum (3 * N) + 1) + (N : ℝ) ^ (19 / 12 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left
        (add_le_add_left hprofile (12 * (N : ℝ) * (L + E + 2 : ℝ) ^ 2 * (pivotSum (3 * N) + 1)))
        (sq_nonneg ((2 ^ L : ℝ)⁻¹))
      exact hfinite.trans (by simpa only [add_comm] using hh)
    _ ≤ ((((2 : ℝ) ^ C) ^ 2) * (N : ℝ) ^ (-2 : ℝ)) *
        (12 * (N : ℝ) * (L + E + 2 : ℝ) ^ 2 * (pivotSum (3 * N) + 1) + (N : ℝ) ^ (19 / 12 : ℝ)) :=
      mul_le_mul_of_nonneg_right hnom (by
        exact add_nonneg (mul_nonneg (by positivity) (by linarith only [pivotSum_nonneg (3 * N)]))
          (Real.rpow_nonneg hn.le _))
    _ = _ := by
      rw [mul_add]
      congr 1
      · rw [Real.rpow_neg hn.le, Real.rpow_two]
        field_simp
      · rw [mul_assoc, ← Real.rpow_add hn]
        norm_num

theorem uniform_upper_from_profile (C D : ℝ) (hD : 0 < D) (A : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, ∀ hN : max N₀ 2 ≤ N, ∀ L E : ℕ, ∀ hL : 1 ≤ L,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N →
      CriticalRawValueProfileUnderInputs.mass N (L + E + 1) ≤ (N : ℝ) ^ (19 / 12 : ℝ) →
      Real.log N ^ A * cost (data (E := E) (by omega : 2 ≤ N) hL) ≤ 1 := by
  let K : ℝ := ((2 : ℝ) ^ C) ^ 2
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨NR, _hNR, hr⟩ := ElementaryReciprocalPivotUpper.uniform_logarithmic_upper (A + 3)
  obtain ⟨NW, hw⟩ := SaddleLogPrefactors.logarithmic_width_le_height D
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NL, hl⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop (max 1 (48 * K * D ^ 2))))
  have hrawT := (isLittleO_log_rpow_rpow_atTop (A : ℝ) (by norm_num : (0 : ℝ) < 5 / 12)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NS, hs⟩ := eventually_atTop.mp (hrawT.bound (by positivity : 0 < 1 / (4 * K)))
  refine ⟨max NR (max NW (max NL NS)), ?_⟩
  intro N hN L E hL hcrit hwidth hprofile
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog1 : 1 ≤ Real.log N := (le_max_left _ _).trans (hl N (by omega))
  have hlog : 0 < Real.log N := by linarith only [hlog1]
  have hlogK : 48 * K * D ^ 2 ≤ Real.log N := (le_max_right _ _).trans (hl N (by omega))
  have hB : L + E + 2 ≤ N := by exact_mod_cast hwidth.trans (hw N (by omega))
  have hbound := profile_upper (by omega : 2 ≤ N) hL hB hcrit hprofile
  let B : ℝ := L + E + 2
  change cost (data (E := E) (by omega : 2 ≤ N) hL) ≤
    12 * K * B ^ 2 * (pivotSum (3 * N) + 1) / N + K * (N : ℝ) ^ (-5 / 12 : ℝ) at hbound
  have hwidthB : B ≤ D * Real.log N := by simpa only [B, Nat.cast_add, Nat.cast_ofNat] using hwidth
  have hR := hr N (by omega)
  have hratio : Real.log N ^ (A + 2) * (pivotSum (3 * N) + 1) / N ≤ 1 / Real.log N := by
    apply (div_le_div_iff₀ hn hlog).mpr
    calc
      _ = Real.log N ^ (A + 3) * (pivotSum (3 * N) + 1) := by
        rw [show A + 3 = (A + 2) + 1 by omega, pow_succ]
        ring
      _ ≤ 1 * (N : ℝ) := by simpa only [one_mul] using hR
  have hlead : Real.log N ^ A * (12 * K * B ^ 2 * (pivotSum (3 * N) + 1) / N) ≤ 1 / 4 := by
    calc
      _ ≤ Real.log N ^ A * (12 * K * (D * Real.log N) ^ 2 * (pivotSum (3 * N) + 1) / N) := by
        gcongr
        linarith only [pivotSum_nonneg (3 * N)]
      _ = 12 * K * D ^ 2 * (Real.log N ^ (A + 2) * (pivotSum (3 * N) + 1) / N) := by
        rw [pow_add]
        ring
      _ ≤ 12 * K * D ^ 2 * (1 / Real.log N) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ 1 / 4 := by
        rw [show 12 * K * D ^ 2 * (1 / Real.log N) = (12 * K * D ^ 2) / Real.log N by ring]
        exact (div_le_iff₀ hlog).mpr (by linarith only [hlogK])
  have hraw : Real.log N ^ A * (K * (N : ℝ) ^ (-5 / 12 : ℝ)) ≤ 1 / 4 := by
    have hh := hs N (by omega)
    have hh' : Real.log N ^ A ≤ (1 / (4 * K)) * (N : ℝ) ^ (5 / 12 : ℝ) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, Real.rpow_natCast,
        abs_of_nonneg (by positivity : 0 ≤ Real.log N ^ A),
        abs_of_nonneg (Real.rpow_nonneg hn.le (5 / 12))] using hh
    calc
      _ ≤ ((1 / (4 * K)) * (N : ℝ) ^ (5 / 12 : ℝ)) * (K * (N : ℝ) ^ (-5 / 12 : ℝ)) :=
        mul_le_mul_of_nonneg_right hh' (by positivity)
      _ = (1 / (4 * K)) * K * ((N : ℝ) ^ (5 / 12 : ℝ) * (N : ℝ) ^ (-5 / 12 : ℝ)) := by ring
      _ = 1 / 4 := by rw [← Real.rpow_add hn]; norm_num; field_simp
  have hh := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ Real.log N ^ A)
  nlinarith only [hh, hlead, hraw]

end PaperP1.ElementarySignedCostUpper
