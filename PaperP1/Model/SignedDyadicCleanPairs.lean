module

public import PaperP1.Model.SignedPrivateCleanCost
public import PaperP1.Model.SignedPrivateDyadicField
public import PaperP1.Model.ForcingExceptionalSets
public import PaperP1.Arithmetic.CleanPivotPairs

/-! # Actual clean boundary pairs contribute to the specified dyadic cost

The two discarded populations are the literal small-pivot boundary set
and the literal non-surjective raw-matrix pair set. Each survivor is
lifted injectively to the zero-excess, prescribed-sign mark pair in the
original retained field.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedDyadicCleanPairs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.OddPrimePivot
  PaperP1.SignedPrivateField PaperP1.SignedPrivateDyadicField
  PaperP1.SignedExactWords PaperP1.ForcingExceptionalSets

local instance signedDyadicCleanPairsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def zeroIndex {G : Finset ℕ} (E : ℕ) (j : G) (s : F₂) : Index G E := (j, (0, s))

def liftPair {G : Finset ℕ} (E : ℕ) (P : Finset (ℕ × ℕ))
    (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) (s : F₂) (p : P) : Index G E × Index G E :=
  (zeroIndex E ⟨p.1.1, (hG p.1 p.2).1⟩ s, zeroIndex E ⟨p.1.2, (hG p.1 p.2).2⟩ s)

theorem liftPair_injective {G : Finset ℕ} (E : ℕ) (P : Finset (ℕ × ℕ))
    (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) (s : F₂) :
    Function.Injective (liftPair E P hG s) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Index G E × Index G E ↦ z.1.1.val) h
  · exact congrArg (fun z : Index G E × Index G E ↦ z.2.1.val) h

def liftedPairs {G : Finset ℕ} (E : ℕ) (P : Finset (ℕ × ℕ))
    (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) (s : F₂) : Finset (Index G E × Index G E) :=
  univ.image (liftPair E P hG s)

theorem liftedPairs_card {G : Finset ℕ} (E : ℕ) (P : Finset (ℕ × ℕ))
    (hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G) (s : F₂) :
    (liftedPairs E P hG s).card = P.card := by
  rw [liftedPairs, card_image_of_injective _ (liftPair_injective E P hG s), card_univ,
    Fintype.card_coe]

theorem retained_of_not_bad {N L E Y j : ℕ} (hN : 2 ≤ N)
    (hY : pivotCutoff L E ≤ Y) (hj : j ∈ boundaryBlock N)
    (hn : j ∉ badBoundaries N (L + E + 2) Y) : j ∈ retainedBoundaries N L E := by
  have hx := (mem_boundaryBlock hN).mp hj
  have hg : ∀ i : Fin (L + E + 2), Y < largestOddPrime (j + i.val) := by
    intro i
    by_contra hi
    exact hn ((mem_badBoundaries hN).mpr ⟨hj, i, by omega⟩)
  refine mem_image.mpr ⟨j + 1, mem_filter.mpr ⟨hx, ?_⟩, by omega⟩
  intro i
  simpa only [Nat.add_sub_cancel] using hY.trans_lt (hg i)

def otherPivots (L j : ℕ) : Finset ℕ :=
  (univ.erase (0 : Fin (L + 2))).image (fun i ↦ largestOddPrime (j + i.val))

def survivingPairs (N L E Y : ℕ) (J : Finset ℕ) : Finset (ℕ × ℕ) :=
  PaperP1.CleanPivotPairs.survivors J (N - 2) N (L + 2) largestOddPrime (otherPivots L)
    (badBoundaries N (L + E + 2) Y)
    (dependentBoundaryPairs (cylinderCutoff N L E) N (L + 2) (L + 2))

theorem surviving_metadata {N L E Y : ℕ} {J : Finset ℕ}
    (hN : 2 ≤ N) (hY : pivotCutoff L E ≤ Y)
    (hJ : J ⊆ boundaryBlock N)
    (hgood : ∀ j ∈ J, j ∉ badBoundaries N (L + E + 2) Y)
    {p : ℕ × ℕ} (hp : p ∈ survivingPairs N L E Y J) :
    p.1 ∈ retainedBoundaries N L E ∧ p.2 ∈ retainedBoundaries N L E ∧
    Function.Surjective (PaperP1.RawWordObservation.joint (cylinderCutoff N L E)
      (fun i : Fin (L + 2) ↦ p.1 + i.val) (fun i : Fin (L + 2) ↦ p.2 + i.val)) := by
  obtain ⟨hp, hn⟩ := mem_sdiff.mp hp
  obtain ⟨hj, hclean⟩ := PaperP1.CleanPivotPairs.mem_pairs.mp hp
  have hjB := hJ hj
  have hkI := (PaperP1.CleanPivotTargets.mem_targets.mp hclean).1
  have hkB : p.2 ∈ boundaryBlock N := by rwa [boundaryBlock_eq_interval hN]
  have hkbad : p.2 ∉ badBoundaries N (L + E + 2) Y := by
    intro hk
    exact hn (mem_union_left _ (mem_product.mpr ⟨hj, hk⟩))
  refine ⟨retained_of_not_bad hN hY hjB (hgood p.1 hj),
    retained_of_not_bad hN hY hkB hkbad, ?_⟩
  by_contra hs
  exact hn (mem_union_right _ ((mem_dependentBoundaryPairs hN).mpr ⟨hjB, hkB, hs⟩))

theorem surjective_joint_ne {M L j k : ℕ}
    (h : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (L + 2) ↦ j + i.val) (fun i : Fin (L + 2) ↦ k + i.val))) : j ≠ k := by
  intro hjk
  subst k
  obtain ⟨ω, hω⟩ := h (0, 1)
  have hz := congrFun (congrArg Prod.fst hω) (0 : Fin (L + 2))
  have ho := congrFun (congrArg Prod.snd hω) (0 : Fin (L + 2))
  change valueBit ω j = 0 at hz
  change valueBit ω j = 1 at ho
  exact zero_ne_one (hz.symm.trans ho)

theorem actual_cost_lower {N L E Y : ℕ} {J : Finset ℕ}
    (hN : 2 ≤ N) (hL : 1 ≤ L) (hY : pivotCutoff L E ≤ Y)
    (hJ : J ⊆ boundaryBlock N)
    (hgood : ∀ j ∈ J, j ∉ badBoundaries N (L + E + 2) Y) (s : F₂) :
    (signedMarkRate L 0) ^ 2 * (survivingPairs N L E Y J).card ≤
      PaperP1.SignedPrivateField.cost (data (E := E) hN hL) := by
  let P := survivingPairs N L E Y J
  let G := retainedBoundaries N L E
  have hmeta := fun p hp ↦ surviving_metadata hN hY hJ hgood (p := p) hp
  have hG : ∀ p ∈ P, p.1 ∈ G ∧ p.2 ∈ G := fun p hp ↦ ⟨(hmeta p hp).1, (hmeta p hp).2.1⟩
  let Q := liftedPairs E P hG s
  have hQ : Q ⊆ PaperP1.PositiveForcingCostLower.directed univ := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
    intro he
    have hn := surjective_joint_ne (hmeta p.val p.property).2.2
    exact hn (congrArg (fun z : Index G E ↦ z.1.val) he).symm
  have hc : ∀ a ∈ Q, ∃ i : Fin (L + a.1.2.1.val + 2),
      a.2.1.val ∈ PaperP1.CleanPivotTargets.targets (N - 2) N
        (pivots (data hN hL) a.1 i).val.val (L + a.2.2.1.val + 2)
        (PaperP1.PrivatePivotTargetFlip.otherPrimes (pivots (data hN hL) a.1) i) := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    refine ⟨0, ?_⟩
    exact (PaperP1.CleanPivotPairs.mem_pairs.mp (mem_sdiff.mp p.property).1).2
  have hjoint : ∀ a ∈ Q, Function.Surjective (PaperP1.RawWordObservation.joint
      (cylinderCutoff N L E)
      (fun i : Fin (L + a.1.2.1.val + 2) ↦ a.1.1.val + i.val)
      (fun i : Fin (L + a.2.2.1.val + 2) ↦ a.2.1.val + i.val)) := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    exact (hmeta p.val p.property).2.2
  have hz : ∀ a ∈ Q, a.1.2.1.val = 0 ∧ a.2.2.1.val = 0 := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    exact ⟨rfl, rfl⟩
  have h := PaperP1.SignedPrivateCleanCost.selected_zero_pairs_lower (data hN hL) Q hQ hc hjoint hz
  rw [liftedPairs_card] at h
  exact h

end PaperP1.SignedDyadicCleanPairs
