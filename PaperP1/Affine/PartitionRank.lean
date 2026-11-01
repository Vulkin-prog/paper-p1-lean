module

public import PaperP1.Algebra.SubspaceFamilyRank
public import PaperP1.Affine.DirectPartitions

/-! # Rank additivity on every restriction of a direct partition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U]
  [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) (P : Finpartition (univ : Finset ι))

omit [FiniteDimensional 𝔽₂ U] in
theorem relationAddition_injective_of_le {κ : Type*} [Fintype κ]
    (T R : κ → Submodule 𝔽₂ U) (hTR : ∀ i, T i ≤ R i) (hinj : Function.Injective (relationAddition R)) :
    Function.Injective (relationAddition T) := by
  let f : ((i : κ) → T i) → ((i : κ) → R i) := fun w i ↦ ⟨(w i).val, hTR i (w i).property⟩
  have hf : Function.Injective f := by
    intro w z hwz
    funext i
    have hval := congrArg (fun v : R i ↦ v.val) (congrFun hwz i)
    exact Subtype.ext hval
  intro w z hwz
  apply hf
  apply hinj
  exact hwz

omit [FiniteDimensional 𝔽₂ U] in
theorem restricted_block_ranges (A : Finset ι) :
    LinearMap.range (relationAddition (fun C : P.parts ↦ span S (C.val ∩ A))) = span S A := by
  rw [range_relationAddition]
  apply le_antisymm
  · exact iSup_le fun C ↦ span_mono S inter_subset_right
  · refine iSup_le fun i ↦ ?_
    let C : P.parts := ⟨P.part i.val, P.part_mem.mpr (mem_univ _)⟩
    exact le_iSup_of_le C (local_le_span S (C.val ∩ A)
      (mem_inter.mpr ⟨P.mem_part (mem_univ i.val), i.property⟩))

theorem rank_partition_inter (hP : RelationDirectPartition S P) (A : Finset ι) :
    rank S A = ∑ C : P.parts, rank S (C.val ∩ A) := by
  have hblock : BlockDirectPartition S P := (relationDirect_iff_blockDirect S P).mp hP
  have hinj := (blockDirect_iff_addition_injective S P).mp hblock
  have hle (C : P.parts) : span S (C.val ∩ A) ≤ blockFamily S P C := by
    rw [blockFamily, blockSpace_eq_iSup]
    exact span_mono S inter_subset_left
  have hsmall := relationAddition_injective_of_le
    (fun C : P.parts ↦ span S (C.val ∩ A)) (blockFamily S P) hle hinj
  have hrank := LinearMap.finrank_range_of_inj hsmall
  rw [restricted_block_ranges S P A, Module.finrank_pi_fintype] at hrank
  exact hrank

theorem rank_partition_sum (hP : RelationDirectPartition S P) :
    rank S univ = ∑ C : P.parts, rank S C.val := by
  have h := rank_partition_inter S P hP univ
  simpa only [inter_univ] using h

theorem privateRank_in_part (hP : RelationDirectPartition S P) (C : P.parts) {i : ι} (hi : i ∈ C.val) :
    privateRank S C.val i = privateRank S univ i := by
  classical
  have hfull := rank_partition_sum S P hP
  have herase := rank_partition_inter S P hP (univ.erase i)
  have hsets (D : P.parts) : D.val ∩ (univ.erase i) = D.val.erase i := by
    ext j
    simp only [mem_inter, mem_erase, mem_univ, true_and, and_comm]
  simp_rw [hsets] at herase
  have hpoint (D : P.parts) : rank S D.val = rank S (D.val.erase i) +
      if D = C then privateRank S C.val i else 0 := by
    by_cases hDC : D = C
    · subst D
      rw [ite_eq_left rfl]
      exact (rank_erase_add_private S C.val i).symm
    · have hiD : i ∉ D.val := by
        intro hiD
        have hne : D.val ≠ C.val := fun h ↦ hDC (Subtype.ext h)
        exact disjoint_left.mp (P.disjoint D.property C.property hne) hiD hi
      rw [erase_eq_of_notMem hiD, ite_eq_right hDC, add_zero]
  have hsum : (∑ D : P.parts, rank S D.val) =
      (∑ D : P.parts, rank S (D.val.erase i)) + privateRank S C.val i := by
    rw [sum_congr rfl (fun D _ ↦ hpoint D), sum_add_distrib]
    simp only [sum_ite_eq', mem_univ, ite_true]
  have hprivate := rank_erase_add_private S (univ : Finset ι) i
  omega

end PaperP1.Affine
