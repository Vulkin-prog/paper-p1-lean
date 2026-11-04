module

public import PaperP1.Model.RandomizedHybridBoundaryPairs

/-! # Actual full-private source data for the randomized arithmetic ledger -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedHybridSourceData

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.RandomizedHybridField PaperP1.RandomizedHybridBoundaryPairs

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}

theorem fullPivots_injective (D : Data M Y K G Good anchor) (j : G) (hj : j.val ∈ Good) :
    Function.Injective (fullPivots D j hj) := by
  have hi := PaperP1.PrivatePivotGeometry.pivot_injective
    (fun i : Fin (K + 1) ↦ (D.anchored.window j).small_pos.trans_lt (D.good j hj i))
    (fun i : Fin (K + 1) ↦ (D.anchored.window j).word_width.trans (D.good j hj i).le)
  intro i k h
  exact hi (congrArg (fun p : PrimeUpTo M ↦ p.val.val) h)

theorem forced_pivot_above (D : Data M Y K G Good anchor) {N B Z : ℕ}
    (hN : 2 ≤ N) (hKB : K + 1 ≤ B) (hG : G ⊆ boundaryBlock N)
    (j : G) (hj : j.val ∈ Good) (hn : j.val ∉ badBoundaries N B Z) (i : Fin (K + 1)) :
    Z < (fullPivots D j hj i).val.val := by
  change Z < PaperP1.OddPrimePivot.largestOddPrime (j.val + i.val)
  by_contra hi
  exact hn ((mem_badBoundaries hN).mpr ⟨hG j.property,
    ⟨i.val, by have := i.isLt; omega⟩, Nat.le_of_not_gt hi⟩)

theorem source_conditions (D : Data M Y K G Good anchor) (selected : G → Fin (K + 1))
    {N B Z : ℕ} (hN : 2 ≤ N) (hKB : K + 1 ≤ B) (hG : G ⊆ boundaryBlock N)
    (j : G) (hj : j.val ∈ Good) (hn : j.val ∉ badBoundaries N B Z) :
    Z ≤ selectedPrime D selected j.val ∧
    (∀ r ∈ otherPrimes D selected j.val, Z ≤ r) ∧
    (∀ r ∈ otherPrimes D selected j.val, (selectedPrime D selected j.val).Coprime r) ∧
    (otherPrimes D selected j.val).card ≤ K := by
  have hg : ∀ i : Fin (K + 1), Z ≤ (fullPivots D j hj i).val.val :=
    fun i ↦ (forced_pivot_above D hN hKB hG j hj hn i).le
  rw [selectedPrime_apply D selected j hj, otherPrimes_apply D selected j hj]
  refine ⟨hg (selected j), PaperP1.PrivatePivotTargetFlip.otherPrimes_above _ Z _ hg,
    PaperP1.PrivatePivotTargetFlip.otherPrimes_coprime _ (fullPivots_injective D j hj) _, ?_⟩
  simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
    PaperP1.PrivatePivotTargetFlip.otherPrimes_card (fullPivots D j hj) (selected j)

theorem selectedPrime_pos (D : Data M Y K G Good anchor) (selected : G → Fin (K + 1)) (n : ℕ) :
    0 < selectedPrime D selected n := by
  unfold selectedPrime
  split
  · exact (fullPivots D _ _ (selected _)).property.pos
  · exact Nat.zero_lt_one

theorem reciprocal_lower (D : Data M Y K G Good anchor) (selected : G → Fin (K + 1))
    (J : Finset ℕ) (Q : ℝ) (hQ : ∀ j ∈ J, (selectedPrime D selected j : ℝ) ≤ Q) :
    (J.card : ℝ) / Q ≤ PaperP1.CleanPivotPairs.reciprocalSum J (selectedPrime D selected) := by
  calc
    _ = ∑ _j ∈ J, 1 / Q := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      have hp : (0 : ℝ) < selectedPrime D selected j := by exact_mod_cast selectedPrime_pos D selected j
      exact one_div_le_one_div_of_le hp (hQ j hj)

end PaperP1.RandomizedHybridSourceData
