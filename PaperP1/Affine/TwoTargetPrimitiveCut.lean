module

public import PaperP1.Affine.DisjointBlockNullity

/-! # A primitive family above nonempty prescribed sources has direct target cuts and the exact two-target deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPrimitiveCut

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem disjoint_of_zero_union (A B : Finset ι) (hAB : Disjoint A B)
    (hzero : relativeNullityOn S (A ∪ B) = 0) : Disjoint (span S A) (span S B) := by
  have hA := relativeNullityOn_mono S (subset_union_left : A ⊆ A ∪ B)
  have hB := relativeNullityOn_mono S (subset_union_right : B ⊆ A ∪ B)
  apply (DisjointBlockNullity.additive_iff_disjoint S A B hAB).mp
  omega

theorem disjoint_of_zero_insert (E : Finset ι) (y : ι) (hy : y ∉ E)
    (hzero : relativeNullityOn S (insert y E) = 0) : Disjoint (span S E) (S y) := by
  have h := disjoint_of_zero_union S E {y} (disjoint_singleton_right.mpr hy)
    (by simpa only [union_singleton] using hzero)
  have hsingle : span S {y} = S y := by simp [span]
  rwa [hsingle] at h

theorem disjoint_of_zero_pair (y z : ι) (hyz : y ≠ z)
    (hzero : relativeNullityOn S {y, z} = 0) : Disjoint (S y) (S z) := by
  let : FiniteDimensional 𝔽₂ (S y) := Module.Finite.of_finite
  rw [RetainedNullity.nullity_pair_eq_intersection S y z hyz] at hzero
  exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hzero)

theorem nullity_eq_deficit (E : Finset ι) (y z : ι) (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hzero : relativeNullityOn S E = 0) :
    relativeNullityOn S (insert y (insert z E)) =
      Module.finrank 𝔽₂ (span S E) + Module.finrank 𝔽₂ (S y) + Module.finrank 𝔽₂ (S z) -
        Module.finrank 𝔽₂ ↥(span S E ⊔ (S y ⊔ S z)) := by
  have hE := rank_add_nullity_on S E
  rw [hzero, add_zero] at hE
  have hfull := rank_add_nullity_on S (insert y (insert z E))
  rw [sum_insert (by simp only [mem_insert, not_or]; exact ⟨hyz, hy⟩), sum_insert hz, ← hE] at hfull
  have hspan : span S (insert y (insert z E)) = span S E ⊔ (S y ⊔ S z) := by
    rw [span_insert, span_insert]
    ac_rfl
  change Module.finrank 𝔽₂ (span S (insert y (insert z E))) +
    relativeNullityOn S (insert y (insert z E)) =
      Module.finrank 𝔽₂ (S y) + (Module.finrank 𝔽₂ (S z) + Module.finrank 𝔽₂ (span S E)) at hfull
  rw [hspan] at hfull
  omega

theorem primitive_data (E : Finset ι) (y z : ι) (hy : y ∉ E) (hz : z ∉ E) (hyz : y ≠ z)
    (hne : E.Nonempty)
    (hproper : ∀ J : Finset ι, J ⊂ insert y (insert z E) → relativeNullityOn S J = 0) :
    Disjoint (span S E) (S y) ∧ Disjoint (span S E) (S z) ∧ Disjoint (S y) (S z) ∧
      relativeNullityOn S (insert y (insert z E)) =
        Module.finrank 𝔽₂ (span S E) + Module.finrank 𝔽₂ (S y) + Module.finrank 𝔽₂ (S z) -
          Module.finrank 𝔽₂ ↥(span S E ⊔ (S y ⊔ S z)) := by
  let I := insert y (insert z E)
  have hEsub : E ⊆ I := (subset_insert z E).trans (subset_insert y (insert z E))
  have hstrict (J : Finset ι) (hJ : J ⊆ I) (w : ι) (hw : w ∈ I) (hnot : w ∉ J) : J ⊂ I :=
    ssubset_iff_subset_not_subset.mpr ⟨hJ, fun h ↦ hnot (h hw)⟩
  have hEzero : relativeNullityOn S E = 0 :=
    hproper E (hstrict E hEsub y (mem_insert_self _ _) hy)
  have hyzero : relativeNullityOn S (insert y E) = 0 := by
    apply hproper
    exact hstrict _ (by
      intro v hv
      rcases mem_insert.mp hv with hv | hv
      · exact hv ▸ mem_insert_self _ _
      · exact hEsub hv) z
      (mem_insert_of_mem (mem_insert_self _ _)) (by simp only [mem_insert, not_or]; exact ⟨hyz.symm, hz⟩)
  have hzzero : relativeNullityOn S (insert z E) = 0 := by
    apply hproper
    exact hstrict _ (subset_insert _ _) y (mem_insert_self _ _)
      (by simp only [mem_insert, not_or]; exact ⟨hyz, hy⟩)
  have hpairzero : relativeNullityOn S {y, z} = 0 := by
    obtain ⟨w, hw⟩ := hne
    apply hproper
    apply hstrict _ (by
      intro v hv
      rcases mem_insert.mp hv with hv | hv
      · exact hv ▸ mem_insert_self _ _
      · exact (mem_singleton.mp hv) ▸ mem_insert_of_mem (mem_insert_self _ _))
      w (hEsub hw)
    intro hwpair
    rcases mem_insert.mp hwpair with hwy | hwz
    · exact hy (hwy ▸ hw)
    · exact hz ((mem_singleton.mp hwz) ▸ hw)
  exact ⟨disjoint_of_zero_insert S E y hy hyzero, disjoint_of_zero_insert S E z hz hzzero,
    disjoint_of_zero_pair S y z hyz hpairzero, nullity_eq_deficit S E y z hy hz hyz hEzero⟩

end PaperP1.TwoTargetPrimitiveCut
