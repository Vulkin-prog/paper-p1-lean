module

public import PaperP1.Model.NongoodPairSeeds
public import PaperP1.Asymptotics.FiniteGoodPartition

/-! # All nongood dependent pair activation seeds have the literal exponent four-fifths -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NongoodPairJointMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ e ∈ NongoodPairSeeds.families (8 * (L + 1) : ℕ) N L G, infiniteJointMoment L e) ≤
          (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := FiniteGoodPartition.uniform_exceptional 4 C (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := LogHeightAlignedActivity.source_tail_from_five C (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 8 (by norm_num) 1
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NE + NT + NL + NG + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hlarge : 8 * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  have hweak : CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak 4 N (8 * (L + 1)) L) ≤
      (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    apply (sum_le_sum_of_subset_of_nonneg (fun e he ↦ (mem_inter.mp (mem_sdiff.mp he).1).2)
      (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans
    exact ht N (by omega) L hband
  have hex := (he N (by omega) L hband).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  calc
    _ ≤ 2 * (CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak 4 N (8 * (L + 1)) L) +
        CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.exceptional 4 N (8 * (L + 1)) L)) :=
      NongoodPairSeeds.joint_bound N L (by omega) hL hlarge G hG
    _ ≤ 4 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by linarith only [hweak, hex]
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.NongoodPairJointMass
