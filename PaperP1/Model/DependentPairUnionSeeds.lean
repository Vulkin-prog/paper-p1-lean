module

public import PaperP1.Model.TwoDependentPairSeeds
public import PaperP1.Model.ActiveFamilySecondMoment
public import PaperP1.Combinatorics.TwoEdgeTripleCover
public import PaperP1.Combinatorics.PairUnionWeights

/-! # Unions of two distinct dependent pairs have no singleton canonical part

Both overlapping and disjoint pairs are included.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairUnionSeeds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RelationCoreWitnesses

def families (E : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (ActiveFamilySecondMoment.ordered E).image (fun p ↦ p.1 ∪ p.2)

theorem family_data (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ))
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e)
    (I : Finset ℕ) (hI : I ∈ families E) :
    I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ 4 ∧
      ∀ C ∈ ActualCanonicalComponents.blocks L I, 2 ≤ C.card := by
  classical
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hI
  obtain ⟨hbox, hne⟩ := mem_filter.mp hp
  obtain ⟨he, hf⟩ := mem_product.mp hbox
  have hedata := hE p.1 he
  have hfdata := hE p.2 hf
  have hcard : (p.1 ∪ p.2).card = 3 ∨ (p.1 ∪ p.2).card = 4 := by
    by_cases hdis : Disjoint p.1 p.2
    · right
      rw [card_union_of_disjoint hdis, hedata.2.1, hfdata.2.1]
    · left
      exact TwoEdgeTripleCover.union_card_three hedata.2.1 hfdata.2.1 hne hdis
  have hcore := TwoDependentPairSeeds.union_core L p.1 p.2 hedata.2.1 hfdata.2.1
    hedata.2.2 hfdata.2.2
  exact ⟨union_subset hedata.1 hfdata.1, by omega, by omega,
    fun C hC ↦ CoreCanonicalComponents.block_card 2 L (by omega) _ hcore C hC⟩

theorem joint_bound (L : ℕ) (E : Finset (Finset ℕ)) :
    (∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2)) ≤
      ∑ I ∈ families E, (4 : ℝ) ^ I.card * infiniteJointMoment L I :=
  PairUnionWeights.weighted_bound _ _ (infiniteJointMoment_nonneg L)

end PaperP1.DependentPairUnionSeeds
