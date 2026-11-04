module

public import PaperP1.Model.ForcingExceptionalSets
public import PaperP1.Arithmetic.DyadicOddPivots
public import PaperP1.Arithmetic.CleanPivotPairs

/-! # Actual clean boundary sources retain the reciprocal mass up to explicit losses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CleanBoundaryReciprocal

open Finset PaperP1.ForcingExceptionalSets PaperP1.CleanPivotPairs
  PaperP1.OddPrimePivot PaperP1.DyadicOddPivots

def sources (N B Y : ℕ) : Finset ℕ := (boundaryBlock N).filter (· ∉ badBoundaries N B Y)

theorem sources_subset (N B Y : ℕ) : sources N B Y ⊆ boundaryBlock N := filter_subset _ _

theorem sources_good {N B Y j : ℕ} (hj : j ∈ sources N B Y) : j ∉ badBoundaries N B Y :=
  (mem_filter.mp hj).2

theorem reciprocal_weight_le_one (n : ℕ) : 1 / (largestOddPrime n : ℝ) ≤ 1 := by
  simpa only [one_div_one] using one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast largestOddPrime_pos n : (1 : ℝ) ≤ largestOddPrime n)

theorem boundary_lower {N : ℕ} (hN : 2 ≤ N) :
    dyadicSum N ≤ reciprocalSum (boundaryBlock N) largestOddPrime + 1 := by
  have hsub : Ico N (2 * N) ⊆ insert (2 * N - 1) (boundaryBlock N) := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := mem_Ico.mp hn
    by_cases heq : n = 2 * N - 1
    · exact mem_insert.mpr (Or.inl heq)
    · apply mem_insert.mpr
      right
      apply (mem_boundaryBlock hN).mpr
      exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hlast : 2 * N - 1 ∉ boundaryBlock N := by
    intro hh
    have hb := (mem_boundaryBlock hN).mp hh
    have hh := (mem_Ico.mp hb).2
    omega
  have hh : dyadicSum N ≤ ∑ n ∈ insert (2 * N - 1) (boundaryBlock N), 1 / (largestOddPrime n : ℝ) :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  rw [sum_insert hlast] at hh
  change dyadicSum N ≤ 1 / (largestOddPrime (2 * N - 1) : ℝ) + reciprocalSum (boundaryBlock N) largestOddPrime at hh
  linarith only [hh, reciprocal_weight_le_one (2 * N - 1)]

theorem remove_bad (N B Y : ℕ) :
    reciprocalSum (boundaryBlock N) largestOddPrime ≤
      reciprocalSum (sources N B Y) largestOddPrime + (badBoundaries N B Y).card := by
  let S := (boundaryBlock N).filter (· ∈ badBoundaries N B Y)
  have hs : S ⊆ badBoundaries N B Y := by intro j hj; exact (mem_filter.mp hj).2
  have hbad : (∑ j ∈ S, 1 / (largestOddPrime j : ℝ)) ≤ (badBoundaries N B Y).card := by
    calc
      _ ≤ ∑ _j ∈ S, (1 : ℝ) := sum_le_sum (fun j _ ↦ reciprocal_weight_le_one j)
      _ = S.card := by simp
      _ ≤ _ := by exact_mod_cast card_le_card hs
  have hsplit := sum_filter_add_sum_filter_not (boundaryBlock N) (fun j ↦ j ∉ badBoundaries N B Y)
    (fun j ↦ 1 / (largestOddPrime j : ℝ))
  have hsplit' : reciprocalSum (sources N B Y) largestOddPrime +
      (∑ j ∈ S, 1 / (largestOddPrime j : ℝ)) = reciprocalSum (boundaryBlock N) largestOddPrime := by
    simpa only [sources, reciprocalSum, S, not_not] using hsplit
  linarith only [hsplit', hbad]

theorem finite_lower {N : ℕ} (hN : 2 ≤ N) (B Y : ℕ) :
    dyadicSum N - 1 - (badBoundaries N B Y).card ≤ reciprocalSum (sources N B Y) largestOddPrime := by
  have hb := boundary_lower hN
  have hd := remove_bad N B Y
  linarith only [hb, hd]

end PaperP1.CleanBoundaryReciprocal
