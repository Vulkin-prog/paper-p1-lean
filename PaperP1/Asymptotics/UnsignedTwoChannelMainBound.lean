module

public import PaperP1.Asymptotics.PositiveSeparatedSourceProfileUnderInputs

/-! # An internal upper power for the exact two-channel positive main term -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnsignedTwoChannelMainBound

open PaperP1.ChannelSumIdentity PaperP1.CriticalBandScale

theorem uniform_main_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      PaperP1.PositiveSeparatedSourceProfileUnderInputs.mainTerm N L ≤ (N : ℝ) ^ (4 / 3 + ε) := by
  let K : ℝ := (2 / 3) * (2 : ℝ) ^ ((C + 1) / 3)
  obtain ⟨NB, hB⟩ := critical_band_scale C
  obtain ⟨NP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le K 2 ε hε
  refine ⟨max NB NP, ?_⟩
  intro N hN L hcrit
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU23 := PaperP1.ChannelUnsignedBound.unsigned_upper_rpow (L := L) (by omega : 0 < 3) (by omega : 2 ≤ 3)
  have hU34 := PaperP1.ChannelUnsignedBound.unsigned_upper_rpow (L := L) (by omega : 0 < 4) (by omega : 3 ≤ 4)
  norm_num only [Nat.cast_ofNat] at hU23 hU34
  have hrootmono : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 4) ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) (L + 1); linarith)
  have hU34' := hU34.trans (mul_le_mul_of_nonneg_left hrootmono (sq_nonneg ((L + 1 : ℕ) : ℝ)))
  have hsum := add_le_add hU23 hU34'
  have hroot : (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 3) ≤
      (2 : ℝ) ^ ((C + 1) / 3) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    simpa only [Nat.cast_ofNat] using PaperP1.CriticalChannelPowers.window_root_upper
      (by omega : 2 ≤ N) (by omega : 0 < 3) hcrit
  have hpoly : K * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ ε := by
    have hp := hP N (by omega) L (hB N (by omega) L hcrit).2
    rw [abs_of_nonneg (by dsimp [K]; positivity : (0 : ℝ) ≤ K * (L + 1 : ℝ) ^ 2)] at hp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  have hpow : (N : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) = (N : ℝ) ^ (4 / 3 : ℝ) := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by ring, Real.rpow_add hn, Real.rpow_one]
  calc
    _ ≤ (N : ℝ) / 3 * (2 * ((L + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / 3)) := by
      unfold PaperP1.PositiveSeparatedSourceProfileUnderInputs.mainTerm
      push_cast
      have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (N : ℝ) / 3)
      push_cast at hh
      nlinarith only [hh]
    _ ≤ (N : ℝ) / 3 * (2 * ((L + 1 : ℕ) : ℝ) ^ 2 *
        ((2 : ℝ) ^ ((C + 1) / 3) * (N : ℝ) ^ (1 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot (by positivity)) (by positivity)
    _ = (K * ((L + 1 : ℕ) : ℝ) ^ 2) * ((N : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ)) := by dsimp [K]; ring
    _ = (K * ((L + 1 : ℕ) : ℝ) ^ 2) * (N : ℝ) ^ (4 / 3 : ℝ) := by rw [hpow]
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (4 / 3 : ℝ) := mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.UnsignedTwoChannelMainBound
