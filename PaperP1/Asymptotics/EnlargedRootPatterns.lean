module

public import PaperP1.Asymptotics.CriticalGeneralRootPatterns
public import PaperP1.Asymptotics.CriticalRootSystemPatterns

/-! # Actual smooth pattern pools at polynomially enlarged critical offset widths

The small-prime cutoff remains linear in the ORIGINAL critical width.
Only offset positions have polynomially enlarged range.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedRootPatterns

open Finset PaperP1.CriticalBandScale

theorem polynomial_offset_factor (C a ε : ℝ) (d J : ℕ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W + 1 ≤ (L + 1) ^ J →
      a * ((W + 1 : ℕ) : ℝ) ^ d ≤ (N : ℝ) ^ ε := by
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  obtain ⟨Np, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le a (J * d) ε hε
  refine ⟨max Ns Np, ?_⟩
  intro N hN L W hcrit hW
  have hWR : ((W + 1 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ J := by exact_mod_cast hW
  have hbound := hp N (by omega) L (hs N (by omega) L hcrit).2
  calc
    _ ≤ a * (((L + 1 : ℕ) : ℝ) ^ J) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hWR d) ha
    _ = a * (L + 1 : ℝ) ^ (J * d) := by rw [← pow_mul]; push_cast; rfl
    _ ≤ _ := (le_abs_self _).trans hbound

theorem general_offsets (C ε : ℝ) (J k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W + 1 ≤ (L + 1) ^ J →
      ((GeneralSplitRadicalPatternPool.leftPatterns k W K ×ˢ
        GeneralSplitRadicalPatternPool.rightPatterns k W K).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A := (((K + 1) * 4 ^ K) ^ k) ^ 2
  obtain ⟨N₀, hN₀⟩ := polynomial_offset_factor C (A : ℝ) ε (K * k + K * k) J (Nat.cast_nonneg _) hε
  refine ⟨N₀, ?_⟩
  intro N hN L W hcrit hW
  have hc : ((GeneralSplitRadicalPatternPool.leftPatterns k W K ×ˢ
      GeneralSplitRadicalPatternPool.rightPatterns k W K).card : ℝ) ≤
      (A : ℝ) * ((W + 1 : ℕ) : ℝ) ^ (K * k + K * k) := by
    exact_mod_cast GeneralSplitRadicalPatternPool.offset_card_bound k W K
  exact hc.trans (hN₀ N hN L W hcrit hW)

theorem linear_offsets (C ε : ℝ) (J k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W + 1 ≤ (L + 1) ^ J →
      ((SplitRadicalPatternPool.leftPatterns k W K ×ˢ
        SplitRadicalPatternPool.rightPatterns k W).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A := ((K + 1) * 4 ^ K * 3) ^ k
  obtain ⟨N₀, hN₀⟩ := polynomial_offset_factor C (A : ℝ) ε ((K + 1) * k) J (Nat.cast_nonneg _) hε
  refine ⟨N₀, ?_⟩
  intro N hN L W hcrit hW
  have hc : ((SplitRadicalPatternPool.leftPatterns k W K ×ˢ
      SplitRadicalPatternPool.rightPatterns k W).card : ℝ) ≤
      (A : ℝ) * ((W + 1 : ℕ) : ℝ) ^ ((K + 1) * k) := by
    exact_mod_cast SplitRadicalPatternPool.offset_card_bound k W K
  exact hc.trans (hN₀ N hN L W hcrit hW)

theorem general_pool (C ε : ℝ) (D J k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W + 1 ≤ (L + 1) ^ J → H ≤ D * (L + 1) →
      ((GeneralSplitRadicalPatternPool.pool k W H K).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨No, ho⟩ := general_offsets C (ε / 2) J k K (by positivity)
  obtain ⟨Nc, hc⟩ := CriticalGeneralRootPatterns.uniform_codes C (ε / 2) D k (by positivity)
  refine ⟨max 1 (max No Nc), ?_⟩
  intro N hN L W H hcrit hW hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [GeneralSplitRadicalPatternPool.pool, card_product, Nat.cast_mul]
  calc
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul (ho N (by omega) L W hcrit hW) (hc N (by omega) L H hcrit hH)
        (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem linear_pool (C ε : ℝ) (D J k K : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → W + 1 ≤ (L + 1) ^ J → H ≤ D * (L + 1) →
      ((SplitRadicalPatternPool.pool k W H K).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨No, ho⟩ := linear_offsets C (ε / 2) J k K (by positivity)
  obtain ⟨Nc, hc⟩ := CriticalRootSystemPatterns.uniform_codes C (ε / 2) D k (by positivity)
  refine ⟨max 1 (max No Nc), ?_⟩
  intro N hN L W H hcrit hW hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [SplitRadicalPatternPool.pool, card_product, Nat.cast_mul]
  calc
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul (ho N (by omega) L W hcrit hW) (hc N (by omega) L H hcrit hH)
        (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem cutoff_height (C : ℝ) (D : ℕ) :
    ∃ A₀ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      (4 ^ H : ℝ) ≤ (N : ℝ) ^ (A₀ : ℝ) := by
  let A₀ := ⌈((D : ℝ) * upperScale) * Real.log 4⌉₊
  obtain ⟨Ns, hs⟩ := critical_band_scale C
  refine ⟨A₀, max 1 Ns, ?_⟩
  intro N hN L H hcrit hH
  have hwidth := (hs N (by omega) L hcrit).2
  have hHR : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hH
  have hcut : (H : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg D)
    nlinarith only [hHR, hh]
  have hfour := SmoothSupportBounds.four_pow_cutoff_le_polynomial (K := A₀) (by omega) hcut (Nat.le_ceil _)
  rw [Real.rpow_natCast]
  exact_mod_cast hfour

theorem general_coefficient_height (C : ℝ) (D : ℕ) :
    ∃ A₀ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ k W K : ℕ, ∀ p ∈ GeneralSplitRadicalPatternPool.pool k W H K, ∀ i,
        ((GeneralSplitRadicalPatternPool.coefficient p i).natAbs : ℝ) ≤ (N : ℝ) ^ (A₀ : ℝ) := by
  obtain ⟨A₀, N₀, h⟩ := cutoff_height C D
  refine ⟨A₀, N₀, ?_⟩
  intro N hN L H hcrit hH k W K p hp i
  have hh : ((GeneralSplitRadicalPatternPool.coefficient p i).natAbs : ℝ) ≤ (4 ^ H : ℝ) := by
    exact_mod_cast GeneralSplitRadicalPatternPool.coefficient_le_four_pow hp i
  exact hh.trans (h N hN L H hcrit hH)

theorem linear_coefficient_height (C : ℝ) (D : ℕ) :
    ∃ A₀ N₀ : ℕ, ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ k W K : ℕ, ∀ p ∈ SplitRadicalPatternPool.pool k W H K, ∀ i,
        ((SplitRadicalPatternPool.coefficient p i).natAbs : ℝ) ≤ (N : ℝ) ^ (A₀ : ℝ) := by
  obtain ⟨A₀, N₀, h⟩ := cutoff_height C D
  refine ⟨A₀, N₀, ?_⟩
  intro N hN L H hcrit hH k W K p hp i
  have hh : ((SplitRadicalPatternPool.coefficient p i).natAbs : ℝ) ≤ (4 ^ H : ℝ) := by
    exact_mod_cast SplitRadicalPatternPool.coefficient_le_four_pow hp i
  exact hh.trans (h N hN L H hcrit hH)

end PaperP1.EnlargedRootPatterns
