module

public import PaperP1.Asymptotics.DyadicPositiveCover
public import PaperP1.Asymptotics.DyadicActualSectorPowers

/-! # Actual nonnegative dyadic profiles have a small remainder after the leading mask

The finite cover is combined with proved full-rank sector powers. The
pointwise domination is later verified for each actual profile weight.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicPositiveRemainder

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedPairRankLoss PaperP1.DyadicAlignedPairMasks

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem channel_square (N L a b : ℕ) : channel N L a b ⊆ (dyadicBlock N) ×ˢ (dyadicBlock N) := filter_subset _ _

theorem high_square (N L q : ℕ) : high N L q ⊆ (dyadicBlock N) ×ˢ (dyadicBlock N) := by
  intro xy hxy
  obtain ⟨ab, _hab, hpair⟩ := mem_biUnion.mp hxy
  exact channel_square N L ab.1 ab.2 hpair

theorem boundary_square (N L : ℕ) : boundary N L ⊆ (dyadicBlock N) ×ˢ (dyadicBlock N) := by
  intro xy hxy
  rcases mem_union.mp (mem_filter.mp hxy).1 with hh | hh
  · exact channel_square N L 1 2 hh
  · exact channel_square N L 2 1 hh

theorem uniform_remainder (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ f : ℕ × ℕ → ℝ,
      (∀ xy, 0 ≤ f xy) →
      (∀ xy ∈ (dyadicBlock N) ×ˢ (dyadicBlock N), f xy ≤ (2 ^ pairLoss xy.1 xy.2 L : ℝ)) →
      0 ≤ (∑ xy ∈ aligned N L, f xy) - (∑ xy ∈ leading N L, f xy) ∧
      (∑ xy ∈ aligned N L, f xy) - (∑ xy ∈ leading N L, f xy) ≤ (N : ℝ) ^ (5 / 4 + ε) := by
  obtain ⟨MC, hC⟩ := PaperP1.DyadicPositiveCover.uniform_bound C
  obtain ⟨ML, hL⟩ := PaperP1.DyadicActualSectorPowers.height_one C (ε / 2) (by positivity)
  obtain ⟨MB, hB⟩ := PaperP1.DyadicActualSectorPowers.boundary C (ε / 2) (by positivity)
  obtain ⟨MH, hH⟩ := PaperP1.DyadicActualSectorPowers.high_height_four C (ε / 2) (by positivity)
  obtain ⟨MF, hF⟩ := PaperP1.HalfCountSchedule.factor_absorption 3 (5 / 4 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max MC (max ML (max MB (max MH MF))), ?_⟩
  intro N hN L hcrit f hf hpoint
  obtain ⟨hclo, hchi⟩ := hC N (by omega) L hcrit f hf
  have hl : (∑ xy ∈ separated (channel N L 1 1) L, f xy) ≤ (N : ℝ) ^ (1 + ε / 2) :=
    (sum_le_sum (fun xy hxy ↦ hpoint xy (channel_square N L 1 1 (mem_filter.mp hxy).1))).trans
      (hL N (by omega) L hcrit)
  have hb : (∑ xy ∈ boundary N L, f xy) ≤ (N : ℝ) ^ (1 / 2 + ε / 2) :=
    (sum_le_sum (fun xy hxy ↦ hpoint xy (boundary_square N L hxy))).trans (hB N (by omega) L hcrit)
  have hh : (∑ xy ∈ separated (high N L 4) L, f xy) ≤ (N : ℝ) ^ (5 / 4 + ε / 2) := by
    have hdom : (∑ xy ∈ separated (high N L 4) L, f xy) ≤
        ∑ xy ∈ separated (high N L 4) L, (2 ^ pairLoss xy.1 xy.2 L : ℝ) :=
      sum_le_sum (fun xy hxy ↦ hpoint xy (high_square N L 4 (mem_filter.mp hxy).1))
    have hsub : separated (high N L 4) L ⊆ high N L 4 := filter_subset _ _
    exact hdom.trans ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)).trans (hH N (by omega) L hcrit))
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlpower : (N : ℝ) ^ (1 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hbpower : (N : ℝ) ^ (1 / 2 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hfpower : 3 * (N : ℝ) ^ (5 / 4 + ε / 2) ≤ (N : ℝ) ^ (5 / 4 + ε) := by
    simpa only [show (5 : ℝ) / 4 + ε / 2 + ε / 2 = 5 / 4 + ε by ring] using hF N (by omega)
  exact ⟨sub_nonneg.mpr hclo,
    hchi.trans ((by linarith only [hl.trans hlpower, hb.trans hbpower, hh] : _ ≤ 3 * (N : ℝ) ^ (5 / 4 + ε / 2)).trans hfpower)⟩

end PaperP1.DyadicPositiveRemainder
