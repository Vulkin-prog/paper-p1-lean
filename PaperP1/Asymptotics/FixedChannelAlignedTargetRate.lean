module

public import PaperP1.Asymptotics.FixedChannelAlignedTargetMass

/-! # The complete fixed-channel aligned target mass, including endpoint sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelAlignedTargetRate

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedChannelGamma PaperP1.DyadicEndpointPairs
  PaperP1.FixedChannelAlignedTargetMass

theorem uniform_bound (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      channelMass N a b L ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε) := by
  classical
  let δ := ε / 10
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb : 3 ≤ b := by omega
  have hγ : 0 ≤ gammaReal a b := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans
    (FixedChannelGammaLower.gammaReal_ge_one_third ha hab hb2a hcop)
  obtain ⟨NR, hr⟩ := AlignedTargetRank.uniform_core C 1 (by norm_num) ha hb hcop hab b
  obtain ⟨NP, _hNP, hp⟩ := uniform_point ha hab hcop hb C δ hδ
  obtain ⟨NQ, _hNQ, hq⟩ := UnitChannelPairWeights.uniform_joint C δ a b ha hab hcop hδ
  obtain ⟨NS, hs⟩ := uniform_polynomial C ((2 * (a + b) + 1 : ℕ) : ℝ) δ (Nat.cast_nonneg _) 1 hδ
  obtain ⟨NZ, hz⟩ := uniform_polynomial C ((6 * a : ℕ) : ℝ) δ (Nat.cast_nonneg _) 15 hδ
  obtain ⟨NE, he⟩ := uniform_polynomial C ((6 * (a + b) + 2 : ℕ) : ℝ) δ (Nat.cast_nonneg _) 7 hδ
  obtain ⟨NI, hi⟩ := uniform_polynomial C 1 δ (by norm_num) 2 hδ
  obtain ⟨NA, hAbsorb⟩ := HalfCountSchedule.factor_absorption 2
    (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NR (max NP (max NQ (max NS (max NZ (max NE (max NI NA))))))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcore := hr N (by omega) L hband
  have hE : ((AlignedTargetRank.endpointSources N a b L).card : ℝ) ≤ (N : ℝ) ^ δ := by
    have hh : ((AlignedTargetRank.endpointSources N a b L).card : ℝ) ≤
        ((6 * (a + b) + 2 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 7 := by exact_mod_cast hcore.1
    exact hh.trans (he N (by omega) L hband)
  have hI : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ δ := by simpa only [one_mul] using hi N (by omega) L hband
  have hEach (i j : Fin (L + 1)) :
      mass N a b L i j ≤ 2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + 4 * δ) := by
    have hS : ((sourcePairs N a b L i j).card : ℝ) ≤ (N : ℝ) ^ (1 + δ) := by
      have hsub : sourcePairs N a b L i j ⊆ FixedChannelSourceGeometry.unitSources N a b L :=
        fun _ hxy ↦ CompressedNonalignedInteractionMass.unit_source i j hxy
      have hcard := (card_le_card hsub).trans (FixedChannelLinearCount.unit_sources_card_linear (by omega) ha)
      have hcast : ((sourcePairs N a b L i j).card : ℝ) ≤
          ((2 * (a + b) + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) * N := by exact_mod_cast hcard
      calc
        _ ≤ (((2 * (a + b) + 1 : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 1) * N := by simpa only [pow_one] using hcast
        _ ≤ (N : ℝ) ^ δ * N := mul_le_mul_of_nonneg_right (hs N (by omega) L hband) hn.le
        _ = (N : ℝ) ^ δ * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
    have hZ : ∀ xy ∈ sourcePairs N a b L i j, (targetSet N a b L i xy).card ≤ (N : ℝ) ^ δ := by
      intro xy hxy
      have hh : ((targetSet N a b L i xy).card : ℝ) ≤ ((6 * a : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 15 := by
        exact_mod_cast target_card (by omega) ha hcop hcore i j hxy
      exact hh.trans (hz N (by omega) L hband)
    have hSource : ∀ xy ∈ sourcePairs N a b L i j,
        infiniteJointMoment L {xy.1, xy.2} ≤ (N : ℝ) ^ (-2 + 1 / (b : ℝ) + δ) := by
      intro xy hxy
      exact hq N (by omega) L hband xy (CompressedNonalignedInteractionMass.unit_source i j hxy)
    have hPoint : ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ targetSet N a b L i xy,
        xy ∉ AlignedTargetRank.endpointSources N a b L →
        infiniteJointMoment L {xy.1, xy.2, z} ≤
          infiniteJointMoment L {xy.1, xy.2} * (N : ℝ) ^ (-1 + gammaReal a b + δ) := by
      intro xy hxy z hzt haway
      obtain ⟨hzN, hzx, hzy, hzA⟩ := mem_filter.mp hzt
      exact hp N (by omega) L hband i j xy hxy z hzN hzx hzy hzA haway
    have hf := finite_bound N a b L i j ((N : ℝ) ^ δ) ((N : ℝ) ^ (-2 + 1 / (b : ℝ) + δ))
      ((N : ℝ) ^ (-1 + gammaReal a b + δ)) (by positivity) (by positivity) (by positivity) hZ hSource hPoint
    have ht1 : ((sourcePairs N a b L i j).card : ℝ) * (N : ℝ) ^ δ *
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + δ) * (N : ℝ) ^ (-1 + gammaReal a b + δ) ≤
          (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + 4 * δ) := by
      calc
        _ ≤ (N : ℝ) ^ (1 + δ) * (N : ℝ) ^ δ * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + δ) *
            (N : ℝ) ^ (-1 + gammaReal a b + δ) := by gcongr
        _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring
    have ht2 : ((AlignedTargetRank.endpointSources N a b L).card : ℝ) * (N : ℝ) ^ δ *
        (N : ℝ) ^ (-2 + 1 / (b : ℝ) + δ) ≤
          (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + 4 * δ) := by
      calc
        _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ δ * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + δ) := by gcongr
        _ = (N : ℝ) ^ (-2 + 1 / (b : ℝ) + 3 * δ) := by
          rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hγ, hδ])
    linarith only [hf, ht1, ht2]
  calc
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), 2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + 4 * δ) :=
      sum_le_sum (fun ij _ ↦ hEach ij.1 ij.2)
    _ = ((L + 1 : ℕ) : ℝ) ^ 2 * (2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + 4 * δ)) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, nsmul_eq_mul, pow_two]
    _ ≤ (N : ℝ) ^ δ * (2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + 4 * δ)) :=
      mul_le_mul_of_nonneg_right hI (by positivity)
    _ = 2 * (N : ℝ) ^ (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 2) := by
      rw [mul_left_comm, ← Real.rpow_add hn]
      congr 2
      dsimp [δ]
      ring
    _ ≤ _ := by
      simpa only [show (-2 + 1 / (b : ℝ) + gammaReal a b + ε / 2) + ε / 2 = -2 + 1 / (b : ℝ) + gammaReal a b + ε by ring] using hAbsorb N (by omega)

end PaperP1.FixedChannelAlignedTargetRate
