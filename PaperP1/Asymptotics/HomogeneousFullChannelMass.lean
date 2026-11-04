module

public import PaperP1.Asymptotics.HomogeneousChannelWeights
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The whole fixed-channel homogeneous source mass, without private filtering -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousFullChannelMass

open Finset PaperP1.Model PaperP1.FixedChannelSourceGeometry

theorem uniform_bound (C ε : ℝ) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ xy ∈ unitSources N a b L, HomogeneousRunMass.probability L {xy.1, xy.2}) ≤
        (N : ℝ) ^ (-1 + 1 / (b : ℝ) + ε) := by
  classical
  obtain ⟨NP, _hNP, hp⟩ := HomogeneousChannelWeights.uniform_pair C (ε / 2) a b ha hab hcop (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NB, hb⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 2) 2 (ε / 2) (by positivity)
  refine ⟨max 2 (max NP (max NS NB)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
      _ = CriticalBandScale.upperScale ^ 2 * (Real.log N) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_ofNat] using hb N (by omega)
  have hcard : ((unitSources N a b L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ 2 * N := by
    exact_mod_cast unit_sources_card (L := L) (b := b) (by omega : 0 < N) ha
  calc
    _ ≤ ∑ _xy ∈ unitSources N a b L, (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      sum_le_sum fun xy hxy ↦ hp N (by omega) L hband xy hxy
    _ = ((unitSources N a b L).card : ℝ) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ 2 * N) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((N : ℝ) ^ (ε / 2) * N) * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + ε / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly hn.le) (by positivity)
    _ = _ := by
      conv_lhs => arg 1; arg 2; rw [← Real.rpow_one (N : ℝ)]
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
      congr 1
      ring

end PaperP1.HomogeneousFullChannelMass
