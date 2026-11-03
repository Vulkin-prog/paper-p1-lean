module

public import PaperP1.Affine.TwoTargetPrimitiveCut
public import PaperP1.Affine.RelativeIntersectionNullity
public import PaperP1.Affine.MinimalSpanCrossing

/-! # Two targets cut from a direct minimal crossing above an internally dependent source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetCrossingCut

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem direct_data (W : Submodule 𝔽₂ U) (E : Finset ι) (y z : ι)
    (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hzero : relativeNullityOn S (insert y (insert z E)) = 0)
    (hproper : ∀ B : Finset ι, B ⊂ insert y (insert z E) → Disjoint W (span S B)) :
    Disjoint (W ⊔ span S E) (S y) ∧ Disjoint (W ⊔ span S E) (S z) ∧ Disjoint (S y) (S z) := by
  have hySub : insert y E ⊆ insert y (insert z E) := insert_subset_insert _ (subset_insert z E)
  have hzSub : insert z E ⊆ insert y (insert z E) := subset_insert _ _
  have hyZero : relativeNullityOn S (insert y E) = 0 := by
    have h := relativeNullityOn_mono S hySub
    omega
  have hzZero : relativeNullityOn S (insert z E) = 0 := by
    have h := relativeNullityOn_mono S hzSub
    omega
  have hzNot : z ∉ insert y E := by simp only [mem_insert, not_or]; exact ⟨hyz.symm, hz⟩
  have hyNot : y ∉ insert z E := by simp only [mem_insert, not_or]; exact ⟨hyz, hy⟩
  have hyStrict : insert y E ⊂ insert y (insert z E) :=
    ssubset_iff_subset_not_subset.mpr ⟨hySub, fun h ↦
      hzNot (h (mem_insert_of_mem (mem_insert_self _ _)))⟩
  have hzStrict : insert z E ⊂ insert y (insert z E) :=
    ssubset_iff_subset_not_subset.mpr ⟨hzSub, fun h ↦
      hyNot (h (mem_insert_self _ _))⟩
  have hwY : Disjoint W (span S E ⊔ S y) := by
    simpa only [span_insert, sup_comm] using hproper (insert y E) hyStrict
  have hwZ : Disjoint W (span S E ⊔ S z) := by
    simpa only [span_insert, sup_comm] using hproper (insert z E) hzStrict
  have hEY := TwoTargetPrimitiveCut.disjoint_of_zero_insert S E y hy hyZero
  have hEZ := TwoTargetPrimitiveCut.disjoint_of_zero_insert S E z hz hzZero
  have hpairSub : ({y, z} : Finset ι) ⊆ insert y (insert z E) := by
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_singleton.mp hi ▸ mem_insert_self _ _)
  have hpairZero : relativeNullityOn S {y, z} = 0 := by
    have h := relativeNullityOn_mono S hpairSub
    omega
  exact ⟨hEY.disjoint_sup_left_of_disjoint_sup_right hwY,
    hEZ.disjoint_sup_left_of_disjoint_sup_right hwZ,
    TwoTargetPrimitiveCut.disjoint_of_zero_pair S y z hyz hpairZero⟩

theorem source_nullity_zero (W : Submodule 𝔽₂ U) [Fintype W] (E : Finset ι) (y z : ι)
    (hy : y ∉ E)
    (hzero : relativeNullityOn S (insert y (insert z E)) = 0)
    (hproper : ∀ B : Finset ι, B ⊂ insert y (insert z E) → Disjoint W (span S B)) :
    MinimalRelativeRelations.nullity W S E = 0 := by
  have hEsub : E ⊆ insert y (insert z E) := (subset_insert z E).trans (subset_insert y _)
  have hEzero : relativeNullityOn S E = 0 := by
    have h := relativeNullityOn_mono S hEsub
    omega
  have hEstrict : E ⊂ insert y (insert z E) :=
    ssubset_iff_subset_not_subset.mpr ⟨hEsub, fun h ↦ hy (h (mem_insert_self _ _))⟩
  exact RelativeIntersectionNullity.zero_of_direct S W E hEzero (hproper E hEstrict)

theorem relative_nullity_eq_deficit (W : Submodule 𝔽₂ U) [Fintype W]
    (E : Finset ι) (y z : ι) (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hsource : MinimalRelativeRelations.nullity W S E = 0) :
    MinimalRelativeRelations.nullity W S (insert y (insert z E)) =
      Module.finrank 𝔽₂ ↥(W ⊔ span S E) + Module.finrank 𝔽₂ (S y) + Module.finrank 𝔽₂ (S z) -
        Module.finrank 𝔽₂ ↥((W ⊔ span S E) ⊔ (S y ⊔ S z)) := by
  have hE := MinimalRelativeRelations.dimension_identity W S E
  rw [hsource, add_zero] at hE
  have hfull := MinimalRelativeRelations.dimension_identity W S (insert y (insert z E))
  rw [sum_insert (by simp only [mem_insert, not_or]; exact ⟨hyz, hy⟩), sum_insert hz] at hfull
  have hspan : W ⊔ span S (insert y (insert z E)) = (W ⊔ span S E) ⊔ (S y ⊔ S z) := by
    rw [span_insert, span_insert]
    ac_rfl
  rw [hspan] at hfull
  omega

theorem data (W : Submodule 𝔽₂ U) [Fintype W] (E : Finset ι) (y z : ι)
    (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hzero : relativeNullityOn S (insert y (insert z E)) = 0)
    (hproper : ∀ B : Finset ι, B ⊂ insert y (insert z E) → Disjoint W (span S B)) :
    Disjoint (W ⊔ span S E) (S y) ∧ Disjoint (W ⊔ span S E) (S z) ∧ Disjoint (S y) (S z) ∧
      MinimalRelativeRelations.nullity W S (insert y (insert z E)) =
        Module.finrank 𝔽₂ ↥(W ⊔ span S E) + Module.finrank 𝔽₂ (S y) + Module.finrank 𝔽₂ (S z) -
          Module.finrank 𝔽₂ ↥((W ⊔ span S E) ⊔ (S y ⊔ S z)) := by
  obtain ⟨hY, hZ, hYZ⟩ := direct_data S W E y z hy hz hyz hzero hproper
  exact ⟨hY, hZ, hYZ, relative_nullity_eq_deficit S W E y z hy hz hyz
    (source_nullity_zero S W E y z hy hzero hproper)⟩

end PaperP1.TwoTargetCrossingCut
