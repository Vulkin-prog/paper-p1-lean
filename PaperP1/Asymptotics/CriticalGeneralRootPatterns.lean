module

public import PaperP1.Arithmetic.GeneralSplitRadicalPatternPool
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Unconditional subpower counts and polynomial coefficient height for actual root-system patterns -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalGeneralRootPatterns

open Finset PaperP1.GeneralSplitRadicalPatternPool PaperP1.CriticalBandScale

theorem uniform_offsets (C ε : ℝ) (k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (((leftPatterns k L K ×ˢ rightPatterns k L K).card : ℕ) : ℝ) ≤ (N : ℝ) ^ ε := by
  let A := (((K + 1) * 4 ^ K) ^ k) ^ 2
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  obtain ⟨Np, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (A : ℝ) (K * k + K * k) ε hε
  refine ⟨max Ns Np, ?_⟩
  intro N hN L hcrit
  have hbound := hp N (by omega) L (hs N (by omega) L hcrit).2
  have hcard : (((leftPatterns k L K ×ˢ rightPatterns k L K).card : ℕ) : ℝ) ≤
      (A : ℝ) * (L + 1 : ℝ) ^ (K * k + K * k) := by exact_mod_cast offset_card_bound k L K
  exact hcard.trans (by simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤
    (A : ℝ) * (L + 1 : ℝ) ^ (K * k + K * k))] using hbound)

theorem uniform_codes (C ε : ℝ) (D k : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ((codePatterns k H).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let η := ε / ((k : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  obtain ⟨Np, hp⟩ := LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually
    ((D : ℝ) * upperScale) (mul_nonneg (Nat.cast_nonneg D) upperScale_pos.le) η hη
  refine ⟨max 1 (max Ns Np), ?_⟩
  intro N hN L H hcrit hH
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwidth := (hs N (by omega) L hcrit).2
  have hcut : (H : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hHR : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hH
    have hmul := mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg D)
    nlinarith only [hHR, hmul]
  have hsupport := hp N (by omega) H hcut
  have hηeq : η * ((k : ℝ) + 1) = ε := div_mul_cancel₀ _ (by positivity)
  have hexp : η * (k : ℝ) ≤ ε := by nlinarith
  calc
    _ = (((PaperP1.DefectCounting.smallPrimesUpTo H).powerset.card : ℕ) : ℝ) ^ k := by
      rw [code_card, Nat.cast_pow]
    _ ≤ ((N : ℝ) ^ η) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hsupport k
    _ = (N : ℝ) ^ (η * (k : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 hexp

theorem uniform_pool (C ε : ℝ) (D k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ((pool k L H K).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨No, ho⟩ := uniform_offsets C (ε / 2) k K (by positivity)
  obtain ⟨Nc, hc⟩ := uniform_codes C (ε / 2) D k (by positivity)
  refine ⟨max 1 (max No Nc), ?_⟩
  intro N hN L H hcrit hH
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hoff := ho N (by omega) L hcrit
  have hcode := hc N (by omega) L H hcrit hH
  calc
    _ = (((leftPatterns k L K ×ˢ rightPatterns k L K).card : ℕ) : ℝ) * (codePatterns k H).card := by
      rw [pool, card_product, Nat.cast_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul hoff hcode (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

theorem uniform_coefficient_height (C : ℝ) (D : ℕ) :
    ∃ A₀ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ k K : ℕ, ∀ p ∈ pool k L H K, ∀ i,
        ((coefficient p i).natAbs : ℝ) ≤ (N : ℝ) ^ (A₀ : ℝ) := by
  let A₀ := ⌈((D : ℝ) * upperScale) * Real.log 4⌉₊
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  refine ⟨A₀, max 1 Ns, ?_⟩
  intro N hN L H hcrit hH k K p hp i
  have hwidth := (hs N (by omega) L hcrit).2
  have hcut : (H : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hHR : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hH
    have hmul := mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg D)
    nlinarith only [hHR, hmul]
  have hfour := SmoothSupportBounds.four_pow_cutoff_le_polynomial (K := A₀) (by omega) hcut (Nat.le_ceil _)
  have hnat := (coefficient_le_four_pow hp i).trans hfour
  rw [Real.rpow_natCast]
  exact_mod_cast hnat

end PaperP1.CriticalGeneralRootPatterns
