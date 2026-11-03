module

public import PaperP1.Model.ConnectedSeedCover

/-! # Actual connected seeds with a variable small-intersection threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VariableConnectedSeedCatalog

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

def families (G : Finset ℕ) (L R : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  (((((Icc 3 R).biUnion (primitiveFamilies G L) ∪ connectedFamilies G L 3) ∪
    LowTwoPairSeeds.families G L η) ∪ DensePairCrossingSeeds.families G L η) ∪
    (Icc 2 (R - 2)).biUnion (DirectCrossingSeedFamilies.families G L))

theorem cover (G : Finset ℕ) (L R : ℕ) (η : ℝ) (hη : 0 ≤ η) (I : Finset ℕ) (hIG : I ⊆ G)
    (hsize : 3 ≤ I.card) (hcap : I.card ≤ R) (hconn : Connected L I) :
    ∃ D ∈ families G L R η, D ⊆ I := by
  classical
  rcases ConnectedSeedCover.cover G L η hη I hIG hsize hconn with hP | hT | hL | hD | hC
  · obtain ⟨D, hDI, hprim, hthree⟩ := hP
    have hm : D ∈ (Icc 3 R).biUnion (primitiveFamilies G L) := mem_biUnion.mpr
      ⟨D.card, mem_Icc.mpr ⟨hthree, (card_le_card hDI).trans hcap⟩,
        mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hDI.trans hIG, rfl⟩, hprim⟩⟩
    exact ⟨D, mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ hm))), hDI⟩
  · obtain ⟨D, hDI, hcard, hconn⟩ := hT
    have hm : D ∈ connectedFamilies G L 3 := mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨hDI.trans hIG, hcard⟩, hconn⟩
    exact ⟨D, mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ hm))), hDI⟩
  · obtain ⟨D, hm, hDI⟩ := hL
    exact ⟨D, mem_union_left _ (mem_union_left _ (mem_union_right _ hm)), hDI⟩
  · obtain ⟨D, hm, hDI⟩ := hD
    exact ⟨D, mem_union_left _ (mem_union_right _ hm), hDI⟩
  · obtain ⟨h, htwo, hcapI, D, hm, hDI⟩ := hC
    exact ⟨D, mem_union_right _ (mem_biUnion.mpr
      ⟨h, mem_Icc.mpr ⟨htwo, hcapI.trans (Nat.sub_le_sub_right hcap 2)⟩, hm⟩), hDI⟩

theorem family_data (G : Finset ℕ) (L R : ℕ) (η : ℝ) (D : Finset ℕ) (hD : D ∈ families G L R η) :
    D ⊆ G ∧ 3 ≤ D.card := by
  classical
  simp only [families, mem_union] at hD
  rcases hD with (((hP | hT) | hL) | hD) | hC
  · obtain ⟨h, hh, hD⟩ := mem_biUnion.mp hP
    obtain ⟨hDG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hD).1
    exact ⟨hDG, hcard.symm ▸ (mem_Icc.mp hh).1⟩
  · obtain ⟨hDG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hT).1
    exact ⟨hDG, hcard.ge⟩
  · have h := LowTwoPairSeeds.family_data G L η D hL
    exact ⟨h.1, by omega⟩
  · have h := DensePairCrossingSeeds.family_data G L η D hD
    exact ⟨h.1, by omega⟩
  · obtain ⟨h, hh, hD⟩ := mem_biUnion.mp hC
    have hd := DirectCrossingSeedFamilies.family_data G L h D hD
    exact ⟨hd.1, by have htwo := (mem_Icc.mp hh).1; omega⟩

theorem mass_bound (G : Finset ℕ) (L R : ℕ) (η : ℝ) :
    (∑ D ∈ families G L R η, infiniteJointMoment L D) ≤
      (∑ h ∈ Icc 3 R, ∑ D ∈ primitiveFamilies G L h, infiniteJointMoment L D) +
      (∑ D ∈ connectedFamilies G L 3, infiniteJointMoment L D) +
      (∑ D ∈ LowTwoPairSeeds.families G L η, infiniteJointMoment L D) +
      (∑ D ∈ DensePairCrossingSeeds.families G L η, infiniteJointMoment L D) +
      ∑ h ∈ Icc 2 (R - 2), ∑ D ∈ DirectCrossingSeedFamilies.families G L h, infiniteJointMoment L D := by
  classical
  let P := (Icc 3 R).biUnion (primitiveFamilies G L)
  let T := connectedFamilies G L 3
  let A := LowTwoPairSeeds.families G L η
  let B := DensePairCrossingSeeds.families G L η
  let C := (Icc 2 (R - 2)).biUnion (DirectCrossingSeedFamilies.families G L)
  have h1 := GraphStarWeights.sum_union_le_nonneg P T (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h2 := GraphStarWeights.sum_union_le_nonneg (P ∪ T) A (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h3 := GraphStarWeights.sum_union_le_nonneg ((P ∪ T) ∪ A) B (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h4 := GraphStarWeights.sum_union_le_nonneg (((P ∪ T) ∪ A) ∪ B) C (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have hp := GraphStarWeights.sum_biUnion_le_nonneg (Icc 3 R) (primitiveFamilies G L)
    (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have hc := GraphStarWeights.sum_biUnion_le_nonneg (Icc 2 (R - 2)) (DirectCrossingSeedFamilies.families G L)
    (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  change (∑ D ∈ (((P ∪ T) ∪ A) ∪ B) ∪ C, infiniteJointMoment L D) ≤ _
  linarith only [h1, h2, h3, h4, hp, hc]

end PaperP1.VariableConnectedSeedCatalog
