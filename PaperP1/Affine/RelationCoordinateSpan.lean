module

public import PaperP1.Affine.RelativeNullity
public import PaperP1.Algebra.SubspaceFamilyRank

/-! # Every coordinate of an effective relation lies in the span of its other coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationCoordinateSpan

open Finset PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]

def otherSpace (S : ι → Submodule 𝔽₂ U) (i : ι) : Submodule 𝔽₂ U :=
  ⨆ j : {j // j ≠ i}, S j.val

theorem coordinate_mem (S : ι → Submodule 𝔽₂ U) (s : (j : ι) → S j)
    (hs : relationAddition S s = 0) (i : ι) : (s i).val ∈ otherSpace S i := by
  have hsum : (∑ j ∈ univ.erase i, (s j).val) ∈ otherSpace S i := by
    apply Submodule.sum_mem
    intro j hj
    have hji := (mem_erase.mp hj).1
    exact (le_iSup (fun j : {j // j ≠ i} ↦ S j.val) ⟨j, hji⟩) (s j).property
  have hz : (∑ j ∈ univ.erase i, (s j).val) + (s i).val = 0 := by
    rw [sum_erase_add univ (fun j ↦ (s j).val) (mem_univ i)]
    exact hs
  have hi : (s i).val = -(∑ j ∈ univ.erase i, (s j).val) :=
    eq_neg_of_add_eq_zero_right hz
  rw [hi]
  exact (otherSpace S i).neg_mem hsum

theorem intersection_ne_bot (S : ι → Submodule 𝔽₂ U) (s : (j : ι) → S j)
    (hs : relationAddition S s = 0) (i : ι) (hi : s i ≠ 0) : S i ⊓ otherSpace S i ≠ ⊥ := by
  intro hbot
  have hmem : (s i).val ∈ S i ⊓ otherSpace S i := ⟨(s i).property, coordinate_mem S s hs i⟩
  rw [hbot] at hmem
  exact hi (Subtype.ext ((Submodule.mem_bot 𝔽₂).mp hmem))

omit [Fintype ι] in
theorem otherSpace_subtype (S : ι → Submodule 𝔽₂ U) (I : Finset ι) (i : I) :
    otherSpace (fun j : I ↦ S j.val) i = SubspaceFamilyRank.span S (I.erase i.val) := by
  classical
  apply le_antisymm
  · refine iSup_le fun j ↦ ?_
    apply SubspaceFamilyRank.local_le_span
    exact mem_erase.mpr ⟨fun h ↦ j.property (Subtype.ext h), j.val.property⟩
  · refine iSup_le fun j ↦ ?_
    have hj := mem_erase.mp j.property
    exact le_iSup (fun k : {k : I // k ≠ i} ↦ S k.val.val)
      ⟨⟨j.val, hj.2⟩, fun h ↦ hj.1 (congrArg Subtype.val h)⟩

omit [Fintype ι] in
theorem full_support_intersection (S : ι → Submodule 𝔽₂ U) (I : Finset ι)
    (s : (j : I) → S j.val) (hs : IsFullSupportRelation (fun j : I ↦ S j.val) s) (i : I) :
    S i.val ⊓ SubspaceFamilyRank.span S (I.erase i.val) ≠ ⊥ := by
  rw [← otherSpace_subtype S I i]
  exact intersection_ne_bot _ s hs.2 i (hs.1 i)

end PaperP1.RelationCoordinateSpan
