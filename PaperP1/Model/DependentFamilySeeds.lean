module

public import PaperP1.Model.PrimitiveActiveSeeds
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Every actually dependent family contains a primitive seed of bounded size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentFamilySeeds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveActiveSeeds

local instance dependentFamilySeedsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def dependentFamilies (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) :=
  (G.powersetCard r).filter fun I ↦ 0 < runRelativeNullity L I

def seededFamilies (G : Finset ℕ) (L r s : ℕ) : Finset (Finset ℕ) :=
  (G.powersetCard r).filter fun I ↦ ∃ D ∈ primitiveFamilies G L s, D ⊆ I

def dependentMass (G : Finset ℕ) (L r : ℕ) : ℝ :=
  ∑ I ∈ dependentFamilies G L r, infiniteJointMoment L I

def seededMass (G : Finset ℕ) (L r s : ℕ) : ℝ :=
  ∑ I ∈ seededFamilies G L r s, infiniteJointMoment L I

theorem seeded_mem {G : Finset ℕ} {L r s : ℕ} {I : Finset ℕ}
    (hI : I ∈ seededFamilies G L r s) :
    I ⊆ G ∧ I.card = r ∧ ∃ D ∈ primitiveFamilies G L s, D ⊆ I := by
  obtain ⟨hcard, hseed⟩ := mem_filter.mp hI
  exact ⟨(mem_powersetCard.mp hcard).1, (mem_powersetCard.mp hcard).2, hseed⟩

theorem primitive_mem {G : Finset ℕ} {L s : ℕ} {D : Finset ℕ}
    (hD : D ∈ primitiveFamilies G L s) : D ⊆ G ∧ D.card = s :=
  mem_powersetCard.mp (mem_filter.mp hD).1

theorem dependent_cover (G : Finset ℕ) (L r : ℕ) :
    dependentFamilies G L r ⊆ (Icc 2 r).biUnion (seededFamilies G L r) := by
  intro I hI
  obtain ⟨hIG, hpos⟩ := mem_filter.mp hI
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
  obtain ⟨D, hDI, hprim⟩ := exists_primitive_subset L I hpos
  have hs : D.card ∈ Icc 2 r := mem_Icc.mpr
    ⟨primitive_card_ge_two L D hprim, (card_le_card hDI).trans hcard.le⟩
  apply mem_biUnion.mpr
  refine ⟨D.card, hs, mem_filter.mpr ⟨hIG, D, ?_, hDI⟩⟩
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hDI.trans hsub, rfl⟩, hprim⟩

theorem dependentMass_le_seeded (G : Finset ℕ) (L r : ℕ) :
    dependentMass G L r ≤ ∑ s ∈ Icc 2 r, seededMass G L r s := by
  exact (sum_le_sum_of_subset_of_nonneg (dependent_cover G L r)
    (fun I _ _ ↦ infiniteJointMoment_nonneg L I)).trans
      (GraphStarWeights.sum_biUnion_le_nonneg (Icc 2 r) (seededFamilies G L r)
        (infiniteJointMoment L) (infiniteJointMoment_nonneg L))

end PaperP1.DependentFamilySeeds
