module

public import PaperP1.Model.AnchoredDyadicField
public import PaperP1.Arithmetic.CleanPivotPairs

/-! # Literal surviving arithmetic pairs in an actual anchored field

The selected nonanchor private prime is an arithmetic function on the
retained sources. Its natural-number extension only labels finite source
sets; outside the retained field its values are never used in a count.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredCleanBoundaryPairs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.AnchoredPrivateValues PaperP1.AnchoredPrivateField

local instance anchoredCleanBoundaryPairsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K + 1)}

def selectedPrime (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j)) (n : ℕ) : ℕ :=
  if hn : n ∈ G then
    (PaperP1.AnchoredWindowForcing.pivots (D.window ⟨n, hn⟩) (selected ⟨n, hn⟩)).val.val else 1

def otherPrimes (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j)) (n : ℕ) : Finset ℕ :=
  if hn : n ∈ G then PaperP1.PrivatePivotTargetFlip.otherPrimes
    (PaperP1.AnchoredWindowForcing.pivots (D.window ⟨n, hn⟩)) (selected ⟨n, hn⟩) else ∅

theorem selectedPrime_apply (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j)) (j : G) :
    selectedPrime D selected j.val =
      (PaperP1.AnchoredWindowForcing.pivots (D.window j) (selected j)).val.val := by
  rw [selectedPrime, dite_eq_left j.property]

theorem otherPrimes_apply (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j)) (j : G) :
    otherPrimes D selected j.val = PaperP1.PrivatePivotTargetFlip.otherPrimes
      (PaperP1.AnchoredWindowForcing.pivots (D.window j)) (selected j) := by
  rw [otherPrimes, dite_eq_left j.property]

def survivingPairs (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j))
    (N B Z : ℕ) (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  PaperP1.CleanPivotPairs.survivors J (N - 2) N (K + 1) (selectedPrime D selected)
    (otherPrimes D selected) (badBoundaries N B Z) (dependentBoundaryPairs M N (K + 1) (K + 1))

theorem surviving_metadata (D : Data M Y K G anchor) (selected : ∀ j : G, Free (anchor j))
    {N B Z : ℕ} {J : Finset ℕ} (hN : 2 ≤ N) (hG : G ⊆ boundaryBlock N)
    (hretain : ∀ n ∈ boundaryBlock N, n ∉ badBoundaries N B Z → n ∈ G) (hJ : J ⊆ G)
    {p : ℕ × ℕ} (hp : p ∈ survivingPairs D selected N B Z J) :
    p.1 ∈ G ∧ p.2 ∈ G ∧ Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ p.1 + i.val) (fun i : Fin (K + 1) ↦ p.2 + i.val)) := by
  obtain ⟨hp, hn⟩ := mem_sdiff.mp hp
  obtain ⟨hj, hc⟩ := PaperP1.CleanPivotPairs.mem_pairs.mp hp
  have hjG := hJ hj
  have hjB := hG hjG
  have hkI := (PaperP1.CleanPivotTargets.mem_targets.mp hc).1
  have hkB : p.2 ∈ boundaryBlock N := by rwa [boundaryBlock_eq_interval hN]
  have hkbad : p.2 ∉ badBoundaries N B Z := fun hk ↦
    hn (mem_union_left _ (mem_product.mpr ⟨hj, hk⟩))
  refine ⟨hjG, hretain p.2 hkB hkbad, ?_⟩
  by_contra hs
  exact hn (mem_union_right _ ((mem_dependentBoundaryPairs hN).mpr ⟨hjB, hkB, hs⟩))

def liftPair (P : Finset (ℕ × ℕ)) (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) (p : P) : G × G :=
  (⟨p.1.1, (hG p.1 p.2).1⟩, ⟨p.1.2, (hG p.1 p.2).2⟩)

theorem liftPair_injective (P : Finset (ℕ × ℕ)) (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) :
    Function.Injective (liftPair P hG) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : G × G ↦ z.1.val) h
  · exact congrArg (fun z : G × G ↦ z.2.val) h

def liftedPairs (P : Finset (ℕ × ℕ)) (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) : Finset (G × G) :=
  univ.image (liftPair P hG)

theorem liftedPairs_card (P : Finset (ℕ × ℕ)) (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) :
    (liftedPairs P hG).card = P.card := by
  rw [liftedPairs, card_image_of_injective _ (liftPair_injective P hG), card_univ, Fintype.card_coe]

theorem joint_surjective_ne {j k : ℕ}
    (h : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ j + i.val) (fun i : Fin (K + 1) ↦ k + i.val))) : j ≠ k := by
  intro hjk
  subst k
  obtain ⟨ω, hω⟩ := h (0, 1)
  have hz := congrFun (congrArg Prod.fst hω) (0 : Fin (K + 1))
  have ho := congrFun (congrArg Prod.snd hω) (0 : Fin (K + 1))
  change valueBit ω j = 0 at hz
  change valueBit ω j = 1 at ho
  exact zero_ne_one (hz.symm.trans ho)

theorem actual_offsite_lower (D : Data M Y K G anchor) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (selected : ∀ j : G, Free (anchor j))
    {N B Z : ℕ} {J : Finset ℕ} (hN : 2 ≤ N) (hG : G ⊆ boundaryBlock N)
    (hretain : ∀ n ∈ boundaryBlock N, n ∉ badBoundaries N B Z → n ∈ G) (hJ : J ⊆ G) :
    (rate K) ^ 2 * (survivingPairs D selected N B Z J).card ≤ offsite D b := by
  let P := survivingPairs D selected N B Z J
  have hm := fun p hp ↦ surviving_metadata D selected hN hG hretain hJ (p := p) hp
  have hmeta : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G := fun p hp ↦ ⟨(hm p hp).1, (hm p hp).2.1⟩
  let Q := liftedPairs P hmeta
  have hQ : Q ⊆ PaperP1.PositiveForcingCostLower.directed univ := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
    intro he
    exact joint_surjective_ne (hm p.val p.property).2.2 (congrArg Subtype.val he).symm
  have hc : ∀ a ∈ Q, ∃ i : Free (anchor a.1),
      a.2.val ∈ PaperP1.CleanPivotTargets.targets (N - 2) N
        (PaperP1.AnchoredWindowForcing.pivots (D.window a.1) i).val.val (K + 1)
        (PaperP1.PrivatePivotTargetFlip.otherPrimes (PaperP1.AnchoredWindowForcing.pivots (D.window a.1)) i) := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    refine ⟨selected ⟨p.val.1, (hmeta p.val p.property).1⟩, ?_⟩
    have ht := (PaperP1.CleanPivotPairs.mem_pairs.mp (mem_sdiff.mp p.property).1).2
    rw [selectedPrime_apply D selected ⟨p.val.1, (hmeta p.val p.property).1⟩,
      otherPrimes_apply D selected ⟨p.val.1, (hmeta p.val p.property).1⟩] at ht
    exact ht
  have hjoint : ∀ a ∈ Q, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ a.1.val + i.val) (fun i : Fin (K + 1) ↦ a.2.val + i.val)) := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    exact (hm p.val p.property).2.2
  have hl := selected_pairs_offsite_lower D hK b Q hQ hc hjoint
  rw [liftedPairs_card] at hl
  exact hl

end PaperP1.AnchoredCleanBoundaryPairs
