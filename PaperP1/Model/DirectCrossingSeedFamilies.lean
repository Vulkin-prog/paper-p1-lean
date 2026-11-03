module

public import PaperP1.Model.MinimalCrossingWindows
public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Actual unordered seeds consisting of a dependent pair and a minimal internally direct crossing -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectCrossingSeedFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

def targets (G : Finset ℕ) (L r : ℕ) (e : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((G \ e).powersetCard r).filter fun A ↦ runRelativeNullity L A = 0 ∧
    span (fun x ↦ squareClassSpace x L) e ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥ ∧
    ∀ B : Finset ℕ, B ⊂ A →
      Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) B)

def families (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) :=
  (DependentFamilySeeds.dependentFamilies G L 2).biUnion fun e ↦ (targets G L r e).image (fun A ↦ e ∪ A)

theorem mem_targets (G : Finset ℕ) (L r : ℕ) (e A : Finset ℕ) :
    A ∈ targets G L r e ↔ A ⊆ G \ e ∧ A.card = r ∧ runRelativeNullity L A = 0 ∧
      span (fun x ↦ squareClassSpace x L) e ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥ ∧
      ∀ B : Finset ℕ, B ⊂ A →
        Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) B) := by
  classical
  simp only [targets, mem_filter, mem_powersetCard]
  exact and_assoc

theorem family_data (G : Finset ℕ) (L r : ℕ) (T : Finset ℕ) (hT : T ∈ families G L r) :
    T ⊆ G ∧ T.card = 2 + r ∧ ∃ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
      ∃ A ∈ targets G L r e, e ∪ A = T := by
  classical
  obtain ⟨e, he, hT⟩ := mem_biUnion.mp hT
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hT
  obtain ⟨heG, heCard⟩ := mem_powersetCard.mp (mem_filter.mp he).1
  obtain ⟨hAG, hACard, _hA⟩ := (mem_targets G L r e A).mp hA
  have hdis : Disjoint e A := disjoint_left.mpr fun x hxe hxA ↦ (mem_sdiff.mp (hAG hxA)).2 hxe
  exact ⟨union_subset heG (hAG.trans sdiff_subset), by rw [card_union_of_disjoint hdis, heCard, hACard], e, he, A, hA, rfl⟩

theorem mass_bound (G : Finset ℕ) (L r : ℕ) :
    (∑ T ∈ families G L r, infiniteJointMoment L T) ≤
      ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
        ∑ A ∈ targets G L r e, infiniteJointMoment L (e ∪ A) := by
  calc
    _ ≤ ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2,
        ∑ T ∈ (targets G L r e).image (fun A ↦ e ∪ A), infiniteJointMoment L T :=
      GraphStarWeights.sum_biUnion_le_nonneg _ _ _ (fun T ↦ infiniteJointMoment_nonneg L T)
    _ ≤ _ := sum_le_sum fun _ _ ↦ sum_image_le_of_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)

end PaperP1.DirectCrossingSeedFamilies
