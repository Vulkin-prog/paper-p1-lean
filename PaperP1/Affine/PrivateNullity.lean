module

public import PaperP1.Algebra.SubspaceFamilyRank
public import PaperP1.Affine.MissingBlockRelations

/-! # Private rank, one-block deletion and the exact number of relations missing that block -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

local instance privateRelationFintype (A : Finset ι) : Fintype (RelationOn S A) := Fintype.ofFinite _
local instance privateRelationDecidableEq (A : Finset ι) : DecidableEq (RelationOn S A) := Classical.decEq _

omit [FiniteDimensional 𝔽₂ U] [DecidableEq ι] in
theorem rank_add_nullity_on (A : Finset ι) :
    rank S A + relativeNullityOn S A = ∑ i ∈ A, Module.finrank 𝔽₂ (S i) := by
  classical
  have h := relativeNullity_dimension_identity (fun i : A ↦ S i.val)
  rw [sum_coe_sort A (fun i ↦ Module.finrank 𝔽₂ (S i))] at h
  exact h.symm

theorem private_nullity_identity (A : Finset ι) {i : ι} (hi : i ∈ A) :
    relativeNullityOn S A + privateRank S A i =
      relativeNullityOn S (A.erase i) + Module.finrank 𝔽₂ (S i) := by
  have hfull := rank_add_nullity_on S A
  have herase := rank_add_nullity_on S (A.erase i)
  have hsum := sum_erase_add A (fun j ↦ Module.finrank 𝔽₂ (S j)) hi
  have hprivate := rank_erase_add_private S A i
  omega

def missedRelations (A : Finset ι) (i : A) : Finset (RelationOn S A) := by
  classical
  exact univ.filter fun w ↦ w.val i = 0

omit [FiniteDimensional 𝔽₂ U] in
theorem erased_kernel_image (A : Finset ι) (i : A) :
    univ.image (subfamilyKernelExtend S (erase_subset i.val A)) = missedRelations S A i := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨v, _, rfl⟩ := mem_image.mp hw
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change subfamilyExtend S (erase_subset i.val A) v.val i = 0
    simp [subfamilyExtend]
  · intro hw
    have hzero (j : A) (hj : j.val ∉ A.erase i.val) : w.val j = 0 := by
      have hji : j = i := by
        apply Subtype.ext
        by_contra hne
        exact hj (mem_erase.mpr ⟨hne, j.property⟩)
      rw [hji]
      exact (mem_filter.mp hw).2
    obtain ⟨v, hv⟩ := subfamilyKernelExtend_has_preimage S (erase_subset i.val A) w hzero
    exact mem_image.mpr ⟨v, mem_univ _, hv⟩

omit [FiniteDimensional 𝔽₂ U] in
theorem card_missedRelations (A : Finset ι) (i : A) :
    (missedRelations S A i).card = 2 ^ relativeNullityOn S (A.erase i.val) := by
  classical
  rw [← erased_kernel_image S A i,
    card_image_of_injective _ (subfamilyKernelExtend_injective S (erase_subset i.val A)), card_univ]
  exact card_relationOn S (A.erase i.val)

end PaperP1.Affine
