module

public import PaperP1.Model.AnchoredPrivateField
public import PaperP1.Model.ForcingExceptionalSets

/-! # The literal retained dyadic population for every arithmetic anchor rule

At most one small pivot is allowed in the maximal support. Every rule
which uses that pivot as anchor when present gives an actual field.
The rule is a fixed function of the integer boundary, before sampling.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredDyadicField

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.OddPrimePivot
  PaperP1.ForcingExceptionalSets PaperP1.AnchoredWindowForcing

local instance anchoredDyadicFieldDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def retainedBoundaries (N B Y : ℕ) : Finset ℕ :=
  (boundaryBlock N).filter fun j ↦ (smallVertices j B Y).card ≤ 1

theorem retained_subset (N B Y : ℕ) : retainedBoundaries N B Y ⊆ boundaryBlock N :=
  filter_subset _ _

theorem retained_card_le (N B Y : ℕ) : (retainedBoundaries N B Y).card ≤ N :=
  (card_le_card (retained_subset N B Y)).trans (boundaryBlock_card_le N)

theorem exists_anchor_rule {N B Y K : ℕ} (hKB : K + 1 ≤ B) :
    ∃ anchor : retainedBoundaries N B Y → Fin (K + 1),
      ∀ j : retainedBoundaries N B Y, ∀ i : Fin (K + 1),
        largestOddPrime (j.val + i.val) ≤ Y → i = anchor j := by
  have ha : ∀ j : retainedBoundaries N B Y, ∃ a : Fin (K + 1),
      ∀ i : Fin (K + 1), largestOddPrime (j.val + i.val) ≤ Y → i = a := by
    intro j
    exact maximal_retention_has_anchor (by omega) hKB (mem_filter.mp j.property).2
  choose anchor hanchor using ha
  exact ⟨anchor, hanchor⟩

theorem data {N B Y K M : ℕ} (hN : 2 ≤ N) (hKB : K + 1 ≤ B) (hBY : B ≤ Y)
    (hM : 2 * N + B ≤ M) (anchor : retainedBoundaries N B Y → Fin (K + 1))
    (hrule : ∀ j : retainedBoundaries N B Y, ∀ i : Fin (K + 1),
      largestOddPrime (j.val + i.val) ≤ Y → i = anchor j) :
    PaperP1.AnchoredPrivateField.Data M Y K (retainedBoundaries N B Y) anchor := {
  window := by
    intro j
    have hx := (mem_boundaryBlock hN).mp ((retained_subset N B Y) j.property)
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hx
    exact data_of_anchor_rule (anchor j) (by omega) (by omega) (by omega)
      (hKB.trans hBY) (hrule j)
  }

theorem retained_of_not_bad {N B Y Z j : ℕ} (hN : 2 ≤ N) (hYZ : Y ≤ Z)
    (hj : j ∈ boundaryBlock N) (hn : j ∉ badBoundaries N B Z) :
    j ∈ retainedBoundaries N B Y := by
  refine mem_filter.mpr ⟨hj, ?_⟩
  have he : smallVertices j B Y = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := (mem_filter.mp hi).2
    exact hn ((mem_badBoundaries hN).mpr ⟨hj, i, hs.trans hYZ⟩)
  rw [he, card_empty]
  omega

theorem retention_ledger {N B Y Z : ℕ} (hN : 2 ≤ N) (hYZ : Y ≤ Z) :
    N ≤ (retainedBoundaries N B Y).card + (badBoundaries N B Z).card := by
  have hc : boundaryBlock N ⊆ retainedBoundaries N B Y ∪ badBoundaries N B Z := by
    intro j hj
    by_cases hb : j ∈ badBoundaries N B Z
    · exact mem_union_right _ hb
    · exact mem_union_left _ (retained_of_not_bad hN hYZ hj hb)
  have h := (card_le_card hc).trans (card_union_le _ _)
  simpa only [boundaryBlock_card hN] using h

theorem indicator_start {N B Y M L : ℕ} (hL : 1 ≤ L)
    (j : retainedBoundaries N B Y) (ω : SampleSpace M) :
    PaperP1.AnchoredPrivateField.indicator (PaperP1.UnsignedAnchoredRunForcing.startWord L 0) j ω =
      decide (StartEvent (valueBit ω) (j.val + 1) L) := by
  have he := PaperP1.UnsignedAnchoredRunForcing.finite_start_word_iff (j := j.val) hL ω
  by_cases hp : PaperP1.BinaryForcingFlip.orbit (PaperP1.UnsignedAnchoredRunForcing.startWord L 0)
      (PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (L + 1) ↦ j.val + i.val) ω)
  · have hb : PaperP1.AnchoredPrivateField.indicator
        (PaperP1.UnsignedAnchoredRunForcing.startWord L 0) j ω = true := decide_eq_true hp
    rw [hb, decide_eq_true (he.mp hp)]
  · have hb : PaperP1.AnchoredPrivateField.indicator
        (PaperP1.UnsignedAnchoredRunForcing.startWord L 0) j ω = false := decide_eq_false hp
    rw [hb, decide_eq_false (fun h ↦ hp (he.mpr h))]

theorem indicator_exact {N B Y M L : ℕ} (hL : 1 ≤ L)
    (j : retainedBoundaries N B Y) (ω : SampleSpace M) :
    PaperP1.AnchoredPrivateField.indicator (PaperP1.SignedExactWords.signedExactWord L 0 0) j ω =
      decide (∃ s : F₂, PaperP1.SignedExactWords.SignedExactMark
        (valueBit ω) (j.val + 1) L 0 s) := by
  have he := PaperP1.UnsignedAnchoredRunForcing.finite_exact_word_iff (j := j.val) hL ω
  by_cases hp : PaperP1.BinaryForcingFlip.orbit (PaperP1.SignedExactWords.signedExactWord L 0 0)
      (PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (L + 2) ↦ j.val + i.val) ω)
  · have hb : PaperP1.AnchoredPrivateField.indicator
        (PaperP1.SignedExactWords.signedExactWord L 0 0) j ω = true := decide_eq_true hp
    rw [hb, decide_eq_true (he.mp hp)]
  · have hb : PaperP1.AnchoredPrivateField.indicator
        (PaperP1.SignedExactWords.signedExactWord L 0 0) j ω = false := decide_eq_false hp
    rw [hb, decide_eq_false (fun h ↦ hp (he.mpr h))]

end PaperP1.AnchoredDyadicField
