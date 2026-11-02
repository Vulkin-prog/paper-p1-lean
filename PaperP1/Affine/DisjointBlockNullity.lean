module

public import PaperP1.Affine.RetainedNullity
public import PaperP1.Affine.DirectPartitions
public import PaperP1.Affine.CanonicalPartConnected

/-! # Exact cross-block nullity and the relation cut of two direct blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointBlockNullity

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem union_nullity (A B : Finset ι) (hAB : Disjoint A B) :
    relativeNullityOn S (A ∪ B) = relativeNullityOn S A + relativeNullityOn S B +
      Module.finrank 𝔽₂ ↥(span S A ⊓ span S B) := by
  let _ := RetainedNullity.span_finite S A
  let _ := RetainedNullity.span_finite S B
  have hA := rank_add_nullity_on S A
  have hB := rank_add_nullity_on S B
  have hU := rank_add_nullity_on S (A ∪ B)
  have hsum := sum_union hAB (f := fun i ↦ Module.finrank 𝔽₂ (S i))
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span S A) (span S B)
  rw [← RetainedNullity.span_union S A B] at hmod
  change rank S (A ∪ B) + Module.finrank 𝔽₂ ↥(span S A ⊓ span S B) = rank S A + rank S B at hmod
  omega

theorem additive_iff_disjoint (A B : Finset ι) (hAB : Disjoint A B) :
    relativeNullityOn S (A ∪ B) = relativeNullityOn S A + relativeNullityOn S B ↔
      Disjoint (span S A) (span S B) := by
  let _ := RetainedNullity.span_finite S A
  let _ := RetainedNullity.span_finite S B
  rw [union_nullity S A B hAB]
  have hzero : relativeNullityOn S A + relativeNullityOn S B +
      Module.finrank 𝔽₂ ↥(span S A ⊓ span S B) = relativeNullityOn S A + relativeNullityOn S B ↔
      Module.finrank 𝔽₂ ↥(span S A ⊓ span S B) = 0 := by omega
  rw [hzero, Submodule.finrank_eq_zero, disjoint_iff]

omit [∀ i, Fintype (S i)] [DecidableEq ι] in
theorem sum_mem_span (A : Finset ι) (s : (i : ι) → S i) :
    (∑ i ∈ A, (s i).val) ∈ span S A :=
  Submodule.sum_mem _ fun i hi ↦ local_le_span S A hi (s i).property

omit [∀ i, Fintype (S i)] in
theorem relation_cut [Fintype ι] (A B : Finset ι) (hAB : Disjoint A B)
    (hcover : A ∪ B = univ) (hspace : Disjoint (span S A) (span S B))
    (s : (i : ι) → S i) (hs : relationAddition S s = 0) :
    (∑ i ∈ A, (s i).val) = 0 := by
  have hsum : (∑ i ∈ A, (s i).val) + (∑ i ∈ B, (s i).val) = 0 := by
    rw [← sum_union hAB, hcover]
    exact hs
  have hB : (∑ i ∈ A, (s i).val) ∈ span S B := by
    rw [eq_neg_of_add_eq_zero_left hsum]
    exact Submodule.neg_mem _ (sum_mem_span S B s)
  have hboth : (∑ i ∈ A, (s i).val) ∈ span S A ⊓ span S B :=
    ⟨sum_mem_span S A s, hB⟩
  rw [hspace.eq_bot] at hboth
  exact hboth

def twoPartPartition [Fintype ι] (A B : Finset ι) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : Disjoint A B) (hcover : A ∪ B = univ) : Finpartition (univ : Finset ι) :=
  (Finpartition.indiscrete hA.ne_empty).extend hB.ne_empty hAB hcover

omit [∀ i, Fintype (S i)] in
theorem twoPartPartition_respects [Fintype ι] (A B : Finset ι)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    (hcover : A ∪ B = univ) (hspace : Disjoint (span S A) (span S B)) :
    RelationDirectPartition S (twoPartPartition A B hA hB hAB hcover) := by
  intro s hs C hC
  change C ∈ ({B, A} : Finset (Finset ι)) at hC
  simp only [mem_insert, mem_singleton] at hC
  rcases hC with hCB | hCA
  · rw [hCB]
    exact relation_cut S B A hAB.symm (by rw [union_comm]; exact hcover) hspace.symm s hs
  · rw [hCA]
    exact relation_cut S A B hAB hcover hspace s hs

omit [∀ i, Fintype (S i)] in
theorem cut_not_connected [Fintype ι] (A B : Finset ι)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B)
    (hcover : A ∪ B = univ) (hspace : Disjoint (span S A) (span S B)) :
    canonicalRelationPartition S ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hA
  let _ : Nonempty ι := ⟨a⟩
  intro hconn
  have hrest : ((univ : Finset ι) \ A).Nonempty := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨b, mem_sdiff.mpr ⟨mem_univ _, fun ha ↦ disjoint_left.mp hAB ha hb⟩⟩
  exact (CanonicalPartConnected.connected_iff_noCut S).mp hconn A ⟨a, ha⟩ hrest
    (fun s hs ↦ relation_cut S A B hAB hcover hspace s hs)

end PaperP1.DisjointBlockNullity
