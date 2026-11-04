module

public import PaperP1.Arithmetic.DyadicAlignedPairMasks

/-! # Actual dyadic full/rational power errors for every fixed-height subfamily

The original ordered roots and both coefficient orientations are kept.
The macroscopic comparison is instantiated on a proved containing interval.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicFixedChannelComparison

open Finset PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.DyadicAlignedPairMasks PaperP1.DyadicMacroscopicTransfer

theorem uniform_error (C : ℝ) (Q q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L a b : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 < a → 0 < b → a.Coprime b →
      q ≤ max a b → a ≤ Q → b ≤ Q → ∀ E : Finset (ℕ × ℕ), E ⊆ channel N L a b →
      (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units a b xy.1 xy.2 L).card - 1)|) ≤
        (N : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by
  obtain ⟨MM, hM⟩ := PaperP1.MacroscopicFixedChannelComparison.uniform_power_error_height
    (C + 1) (1 / 2) (by norm_num) Q q hq (ε / 2) (by positivity)
  obtain ⟨NF, hF⟩ := double_power (1 / 2 + 1 / (q : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MM NF, ?_⟩
  intro N hN L a b hcrit ha hb hab hqmax haQ hbQ E hE
  have hsub := hE.trans (channel_subset_macro (by omega : 2 ≤ N))
  have hm := hM (2 * N) (by omega) L a b (critical_band (by omega : 0 < N) hcrit)
    ha hb hab hqmax haQ hbQ E hsub
  have hf : ((2 * N : ℕ) : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε / 2) ≤
      (N : ℝ) ^ (1 / 2 + 1 / (q : ℝ) + ε) := by
    simpa only [show (1 : ℝ) / 2 + 1 / (q : ℝ) + ε / 2 + ε / 2 = 1 / 2 + 1 / (q : ℝ) + ε by ring] using hF N (by omega)
  exact hm.trans hf

theorem height_three (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ E : Finset (ℕ × ℕ), E ⊆ channel N L 2 3 →
      (∑ xy ∈ E, |(2 ^ pairLoss xy.1 xy.2 L : ℝ) - 2 ^ ((units 2 3 xy.1 xy.2 L).card - 1)|) ≤
        (N : ℝ) ^ (5 / 6 + ε) := by
  obtain ⟨N₀, h⟩ := uniform_error C 3 3 (by omega) ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit E hE
  simpa only [Nat.cast_ofNat, show (1 : ℝ) / 2 + 1 / (3 : ℝ) + ε = 5 / 6 + ε by ring] using
    h N hN L 2 3 hcrit (by omega) (by omega) (by norm_num) (by decide) (by omega) (by omega) E hE

end PaperP1.DyadicFixedChannelComparison
