module

public import PaperP1.Model.SignedDyadicCleanPairs

/-! # The actual source primes discharge the clean arithmetic data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedCleanSourceData

open Finset PaperP1.Arithmetic PaperP1.OddPrimePivot PaperP1.SignedDyadicCleanPairs
  PaperP1.ForcingExceptionalSets PaperP1.PrivatePivotGeometry

theorem source_pivot_above {N L E Y j : ℕ} (hN : 2 ≤ N)
    (hj : j ∈ boundaryBlock N) (hn : j ∉ badBoundaries N (L + E + 2) Y)
    (i : Fin (L + 2)) : Y < largestOddPrime (j + i.val) := by
  by_contra hi
  exact hn ((mem_badBoundaries hN).mpr ⟨hj, ⟨i.val, by have := i.isLt; omega⟩,
    Nat.le_of_not_gt hi⟩)

theorem otherPivots_card (L j : ℕ) : (otherPivots L j).card ≤ L + 1 := by
  calc
    _ ≤ (univ.erase (0 : Fin (L + 2))).card := card_image_le
    _ = L + 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega

theorem source_conditions {N L E Y j : ℕ} (hN : 2 ≤ N) (hY : L + 2 ≤ Y)
    (hj : j ∈ boundaryBlock N) (hn : j ∉ badBoundaries N (L + E + 2) Y) :
    Y ≤ largestOddPrime j ∧
    (∀ r ∈ otherPivots L j, Y ≤ r) ∧
    (∀ r ∈ otherPivots L j, (largestOddPrime j).Coprime r) := by
  have hg := source_pivot_above hN hj hn
  have h1 : ∀ i : Fin (L + 2), 1 < largestOddPrime (j + i.val) := by
    intro i
    exact lt_of_lt_of_le (by omega : 1 < Y) (hg i).le
  have hb : ∀ i : Fin (L + 2), L + 2 ≤ largestOddPrime (j + i.val) :=
    fun i ↦ hY.trans (hg i).le
  have hinj := pivot_injective h1 hb
  refine ⟨by simpa using (hg 0).le, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, _, rfl⟩ := mem_image.mp hr
    exact (hg i).le
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
    apply (Nat.coprime_primes (pivot_spec (h1 0)).1 (pivot_spec (h1 i)).1).mpr
    intro he
    exact (mem_erase.mp hi).1 (hinj he.symm)

end PaperP1.SignedCleanSourceData
