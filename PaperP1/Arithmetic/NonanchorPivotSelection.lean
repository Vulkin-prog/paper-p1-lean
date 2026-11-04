module

public import PaperP1.Arithmetic.OddPrimePivot
public import PaperP1.Model.AnchoredPrivateValues

/-! # Two ordinary smooth candidates leave a small pivot outside every anchor

This is a finite selection statement. It assumes the candidate indices
exist at the specified source; it asserts no short-interval abundance.
The selected index is fixed before sampling the prime signs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonanchorPivotSelection

open Finset PaperP1.Arithmetic PaperP1.OddPrimePivot PaperP1.AnchoredPrivateValues

local instance nonanchorPivotSelectionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def ordinaryIndices (j B : ℕ) (Q : ℝ) : Finset (Fin B) :=
  univ.filter fun i ↦ (largestPrimeFactor (j + i.val) : ℝ) ≤ Q

theorem pivot_le_of_ordinary {j B : ℕ} {Q : ℝ} {i : Fin B} (hi : i ∈ ordinaryIndices j B Q) :
    (largestOddPrime (j + i.val) : ℝ) ≤ Q := by
  have hp : (largestOddPrime (j + i.val) : ℝ) ≤ largestPrimeFactor (j + i.val) := by
    exact_mod_cast largestOddPrime_le_largestPrimeFactor (j + i.val)
  exact hp.trans (mem_filter.mp hi).2

theorem exists_nonanchor {j B : ℕ} {Q : ℝ} (h : 2 ≤ (ordinaryIndices j B Q).card)
    (anchor : Fin B) : ∃ i : Free anchor, (largestOddPrime (j + i.val.val) : ℝ) ≤ Q := by
  obtain ⟨i, hi, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (ordinaryIndices j B Q).card) anchor
  exact ⟨⟨i, hne⟩, pivot_le_of_ordinary hi⟩

theorem exists_selector (G : Finset ℕ) (K : ℕ) (hK : 1 ≤ K)
    (anchor : G → Fin (K + 1)) (Good : G → Prop) (Q : ℝ)
    (h : ∀ j : G, Good j → 2 ≤ (ordinaryIndices j.val (K + 1) Q).card) :
    ∃ selected : ∀ j : G, Free (anchor j),
      ∀ j : G, Good j → (largestOddPrime (j.val + (selected j).val.val) : ℝ) ≤ Q := by
  have hs : ∀ j : G, ∃ i : Free (anchor j),
      Good j → (largestOddPrime (j.val + i.val.val) : ℝ) ≤ Q := by
    intro j
    by_cases hj : Good j
    · obtain ⟨i, hi⟩ := exists_nonanchor (h j hj) (anchor j)
      exact ⟨i, fun _ ↦ hi⟩
    · have hc : 1 < (univ : Finset (Fin (K + 1))).card := by
        simp only [card_univ, Fintype.card_fin]
        omega
      obtain ⟨i, _, hne⟩ := Finset.exists_mem_ne hc (anchor j)
      exact ⟨⟨i, hne⟩, fun hh ↦ False.elim (hj hh)⟩
  choose selected hselected using hs
  exact ⟨selected, hselected⟩

end PaperP1.NonanchorPivotSelection
