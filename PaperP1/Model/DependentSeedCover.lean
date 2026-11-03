module

public import PaperP1.Model.ConnectedSeedCatalog

/-! # Dependent pairs and the completed connected catalog cover every actual dependent family of bounded order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentSeedCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

def families (G : Finset ℕ) (L R : ℕ) : Finset (Finset ℕ) :=
  DependentFamilySeeds.dependentFamilies G L 2 ∪ ConnectedSeedCatalog.families G L R

theorem family_data (G : Finset ℕ) (L R : ℕ) (D : Finset ℕ) (hD : D ∈ families G L R) :
    D ⊆ G ∧ 2 ≤ D.card := by
  rcases mem_union.mp hD with hD | hD
  · obtain ⟨hDG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hD).1
    exact ⟨hDG, hcard.ge⟩
  · have hd := ConnectedSeedCatalog.family_data G L R D hD
    exact ⟨hd.1, by omega⟩

theorem cover (G : Finset ℕ) (L R : ℕ) (I : Finset ℕ) (hIG : I ⊆ G)
    (hcap : I.card ≤ R) (hdep : 0 < runRelativeNullity L I) :
    ∃ D ∈ families G L R, D ⊆ I := by
  classical
  obtain ⟨D, hDI, hprim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L I hdep
  have htwo := PrimitiveActiveSeeds.primitive_card_ge_two L D hprim
  by_cases hcard : D.card = 2
  · exact ⟨D, mem_union_left _ (mem_filter.mpr
      ⟨mem_powersetCard.mpr ⟨hDI.trans hIG, hcard⟩, hprim.1⟩), hDI⟩
  have hthree : 3 ≤ D.card := by omega
  have hm : D ∈ (Icc 3 R).biUnion (primitiveFamilies G L) := mem_biUnion.mpr
    ⟨D.card, mem_Icc.mpr ⟨hthree, (card_le_card hDI).trans hcap⟩,
      mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hDI.trans hIG, rfl⟩, hprim⟩⟩
  exact ⟨D, mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ hm)))), hDI⟩

theorem low_card_empty (G : Finset ℕ) (L r : ℕ) (hr : r ≤ 1) :
    DependentFamilySeeds.dependentFamilies G L r = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro I hI
  obtain ⟨hIG, hdep⟩ := mem_filter.mp hI
  have hcard := (mem_powersetCard.mp hIG).2
  have hz := RetainedNullity.nullity_card_le_one (fun x ↦ squareClassSpace x L) I (by omega)
  exact (ne_of_gt hdep) hz

end PaperP1.DependentSeedCover
