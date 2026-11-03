module

public import PaperP1.Model.TwoTargetJointWeight
public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Combinatorics.GraphStarWeights

/-! # The full literal dense minimal pair-crossing seed population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePairCrossingSeeds

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData

def targets (G : Finset ℕ) (L : ℕ) (η : ℝ) (e : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((G \ e) ×ˢ (G \ e)).filter fun p ↦ p.1 ≠ p.2 ∧
    (∀ B : Finset ℕ, B ⊂ {p.1, p.2} → Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) ∧
    η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓ span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ)

def families (G : Finset ℕ) (L : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  (DependentFamilySeeds.dependentFamilies G L 2).biUnion fun e ↦
    (targets G L η e).image (TwoTargetFamilyCover.family e)

theorem mem_targets (G : Finset ℕ) (L : ℕ) (η : ℝ) (e : Finset ℕ) (p : ℕ × ℕ) :
    p ∈ targets G L η e ↔ p.1 ∈ G ∧ p.2 ∈ G ∧ p.1 ≠ p.2 ∧ p.1 ∉ e ∧ p.2 ∉ e ∧
      (∀ B : Finset ℕ, B ⊂ {p.1, p.2} → Disjoint (sourceSpace e L) (span (fun x ↦ squareClassSpace x L) B)) ∧
      η * L ≤ (Module.finrank F₂ ↥(sourceSpace e L ⊓ span (fun x ↦ squareClassSpace x L) {p.1, p.2}) : ℝ) := by
  classical
  simp only [targets, mem_filter, mem_product, mem_sdiff]
  tauto

theorem family_data (G : Finset ℕ) (L : ℕ) (η : ℝ) (I : Finset ℕ) (hI : I ∈ families G L η) :
    I ⊆ G ∧ I.card = 4 ∧ ∃ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
      ∃ p ∈ targets G L η e, TwoTargetFamilyCover.family e p = I := by
  classical
  obtain ⟨e, he, himage⟩ := mem_biUnion.mp hI
  obtain ⟨p, hp, rfl⟩ := mem_image.mp himage
  have hm := (mem_targets G L η e p).mp hp
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (mem_filter.mp he).1
  refine ⟨?_, ?_, e, he, p, hp, rfl⟩
  · change insert p.1 (insert p.2 e) ⊆ G
    exact insert_subset hm.1 (insert_subset hm.2.1 heG)
  · change (insert p.1 (insert p.2 e)).card = 4
    rw [card_insert_of_notMem (by simp only [mem_insert, not_or]; exact ⟨hm.2.2.1, hm.2.2.2.1⟩),
      card_insert_of_notMem hm.2.2.2.2.1, hecard]

theorem mass_bound (G : Finset ℕ) (L : ℕ) (η : ℝ) :
    (∑ I ∈ families G L η, infiniteJointMoment L I) ≤
      ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
        ∑ p ∈ targets G L η e, infiniteJointMoment L (TwoTargetFamilyCover.family e p) := by
  calc
    _ ≤ ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
        ∑ I ∈ (targets G L η e).image (TwoTargetFamilyCover.family e), infiniteJointMoment L I :=
      GraphStarWeights.sum_biUnion_le_nonneg _ _ _ (fun I ↦ infiniteJointMoment_nonneg L I)
    _ ≤ _ := sum_le_sum fun e _ ↦ sum_image_le_of_nonneg (fun I _ ↦ infiniteJointMoment_nonneg L I)

end PaperP1.DensePairCrossingSeeds
