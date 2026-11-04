module

public import PaperP1.Model.AnchoredCleanBoundaryPairs

/-! # Actual selected nonanchor source primes discharge the arithmetic ledger -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredCleanSourceData

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.AnchoredPrivateValues
  PaperP1.AnchoredPrivateField PaperP1.AnchoredCleanBoundaryPairs PaperP1.ForcingExceptionalSets

variable {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K + 1)}

theorem pivots_injective (D : Data M Y K G anchor) (j : G) :
    Function.Injective (PaperP1.AnchoredWindowForcing.pivots (D.window j)) :=
  PaperP1.AnchoredWindowPivots.injective (D.window j).boundary_pos (D.window j).cutoff (anchor j)
    (fun i ↦ (D.window j).small_pos.trans_lt ((D.window j).good i))
    (fun i ↦ (D.window j).word_width.trans ((D.window j).good i).le)

theorem forced_pivot_above (D : Data M Y K G anchor) {N B Z : ℕ}
    (hN : 2 ≤ N) (hKB : K + 1 ≤ B) (hG : G ⊆ boundaryBlock N)
    (j : G) (hn : j.val ∉ badBoundaries N B Z) (i : Free (anchor j)) :
    Z < (PaperP1.AnchoredWindowForcing.pivots (D.window j) i).val.val := by
  change Z < PaperP1.OddPrimePivot.largestOddPrime (j.val + i.val.val)
  by_contra hi
  exact hn ((mem_badBoundaries hN).mpr ⟨hG j.property,
    ⟨i.val.val, by have := i.val.isLt; omega⟩, Nat.le_of_not_gt hi⟩)

theorem source_conditions (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j))
    {N B Z : ℕ} (hN : 2 ≤ N) (hKB : K + 1 ≤ B) (hG : G ⊆ boundaryBlock N)
    (j : G) (hn : j.val ∉ badBoundaries N B Z) :
    Z ≤ selectedPrime D selected j.val ∧
    (∀ r ∈ otherPrimes D selected j.val, Z ≤ r) ∧
    (∀ r ∈ otherPrimes D selected j.val, (selectedPrime D selected j.val).Coprime r) ∧
    (otherPrimes D selected j.val).card ≤ K := by
  have hg : ∀ i : Free (anchor j), Z ≤
      (PaperP1.AnchoredWindowForcing.pivots (D.window j) i).val.val :=
    fun i ↦ (forced_pivot_above D hN hKB hG j hn i).le
  rw [selectedPrime_apply, otherPrimes_apply]
  refine ⟨hg (selected j), PaperP1.PrivatePivotTargetFlip.otherPrimes_above _ Z _ hg,
    PaperP1.PrivatePivotTargetFlip.otherPrimes_coprime _ (pivots_injective D j) _, ?_⟩
  have hc := PaperP1.PrivatePivotTargetFlip.otherPrimes_card
    (PaperP1.AnchoredWindowForcing.pivots (D.window j)) (selected j)
  rw [PaperP1.AnchoredPrivateForcing.free_card, Fintype.card_fin] at hc
  omega

end PaperP1.AnchoredCleanSourceData
