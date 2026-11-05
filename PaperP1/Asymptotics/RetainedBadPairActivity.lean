module

public import PaperP1.Model.RetainedBoundaryPositiveMass
public import PaperP1.Asymptotics.FiniteGoodPartition

/-! # The literal centered bad-pair activity, including incompatible dependent sources, has exponent four-fifths -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedBadPairActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RetainedBoundaryPositiveMass

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → badActivity (8 * (L + 1) : ℕ) N L ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := FiniteGoodPartition.uniform_exceptional 4 C (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := LogHeightAlignedActivity.source_tail_from_five C (ε / 2) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 8 (by norm_num) 1
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 8 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NE + NT + NL + NG + NF, by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hlarge : 8 * (L + 1) < N := by
    have h := hl N (by omega) L hband
    simp only [pow_one] at h
    exact_mod_cast h
  let W := FiniteGoodChannelPartition.weak 4 N (8 * (L + 1)) L
  let E := FiniteGoodChannelPartition.exceptional 4 N (8 * (L + 1)) L
  have hweak : CompatibleActivitySplit.absolute L W ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    apply (sum_le_sum_of_subset_of_nonneg (fun e he ↦ (mem_inter.mp (mem_sdiff.mp he).1).2)
      (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans
    exact ht N (by omega) L hband
  have hex := (he N (by omega) L hband).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
      (by linarith only [] : (-1 : ℝ) + ε / 2 ≤ -4 / 5 + ε / 2))
  have hsub := NongoodPairSeeds.cover N L (by omega) hlarge (RegularStarts.regularStarts N L)
    (RegularStarts.regularStarts_subset N L)
  have hcover := (sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans
    (GraphStarWeights.sum_union_le_nonneg W E (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _))
  rw [bad_eq_nongood _ N L hL]
  calc
    _ ≤ 8 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
      change (∑ e ∈ NongoodPairSeeds.families (8 * (L + 1) : ℕ) N L (RegularStarts.regularStarts N L),
        |infiniteCenteredCoefficient L e|) ≤ CompatibleActivitySplit.absolute L W + CompatibleActivitySplit.absolute L E at hcover
      linarith only [hcover, hweak, hex]
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RetainedBadPairActivity
