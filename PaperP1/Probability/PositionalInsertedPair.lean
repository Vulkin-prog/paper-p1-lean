module

public import PaperP1.Probability.PositionalDeletionKernels

/-! # One inserted pair is recovered exactly off explicit background events -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalInsertedPair

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalDeletionKernels

variable {ι : Type*}

local instance insertedPairDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def touchingVertices (E : Finset (Finset ι)) (e : Finset ι) : Finset ι :=
  (E.filter (fun f ↦ ¬ Disjoint f e)).biUnion id

theorem mem_touching (E : Finset (Finset ι)) (e : Finset ι) (x : ι) :
    x ∈ touchingVertices E e ↔ ∃ f ∈ E, ¬ Disjoint f e ∧ x ∈ f := by
  constructor
  · intro hx
    obtain ⟨f, hf, hxf⟩ := mem_biUnion.mp hx
    exact ⟨f, (mem_filter.mp hf).1, (mem_filter.mp hf).2, hxf⟩
  · rintro ⟨f, hf, hd, hxf⟩
    exact mem_biUnion.mpr ⟨f, mem_filter.mpr ⟨hf, hd⟩, hxf⟩

theorem touching_subset (E : Finset (Finset ι)) (e G : Finset ι)
    (hE : ∀ f ∈ E, f ⊆ G) : touchingVertices E e ⊆ G := by
  intro x hx
  obtain ⟨f, hf, hxf⟩ := mem_biUnion.mp hx
  exact hE f (mem_filter.mp hf).1 hxf

theorem edge_subset_touching (E : Finset (Finset ι)) (e : Finset ι)
    (he : e ∈ E) (hne : e.Nonempty) : e ⊆ touchingVertices E e := by
  have hself : ¬ Disjoint e e := by
    intro hd
    obtain ⟨x, hx⟩ := hne
    exact disjoint_left.mp hd hx hx
  intro x hx
  exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hself⟩, hx⟩

theorem active_inserted_pair (E : Finset (Finset ι)) (e : Finset ι) (v : Configuration ι)
    (he : e ∈ E) (hE : ∀ f ∈ E, f.card = 2)
    (hno : activeEdges E v = ∅) (hz : ∀ x ∈ touchingVertices E e, v x = 0) :
    activeEdges E (v + edgeVector e) = {e} := by
  classical
  apply subset_antisymm
  · intro f hf
    obtain ⟨hfE, hfactive⟩ := mem_filter.mp hf
    have hsub : f ⊆ e := by
      by_cases hd : Disjoint f e
      · have hold : f ∈ activeEdges E v := by
          apply mem_filter.mpr
          refine ⟨hfE, ?_⟩
          intro x hx
          have hxe : x ∉ e := disjoint_left.mp hd hx
          have hp := hfactive x hx
          simpa only [Finsupp.add_apply, edgeVector_apply, ite_eq_right hxe, add_zero] using hp
        rw [hno] at hold
        exact False.elim (notMem_empty _ hold)
      · intro x hx
        have hxS : x ∈ touchingVertices E e := mem_biUnion.mpr ⟨f, mem_filter.mpr ⟨hfE, hd⟩, hx⟩
        have hp := hfactive x hx
        rw [Finsupp.add_apply, hz x hxS, edgeVector_apply, zero_add] at hp
        by_contra hxe
        rw [ite_eq_right hxe] at hp
        omega
    have hfe : f = e := eq_of_subset_of_card_le hsub (by rw [hE e he, hE f hfE])
    exact mem_singleton.mpr hfe
  · intro f hf
    have hfe := mem_singleton.mp hf
    subst f
    apply mem_filter.mpr
    refine ⟨he, ?_⟩
    intro x hx
    rw [Finsupp.add_apply, edgeVector_apply, ite_eq_left hx]
    omega

theorem delete_inserted (e : Finset ι) (v : Configuration ι) :
    deleteEdge e (v + edgeVector e) = v := by
  rw [deleteEdge, add_tsub_cancel_right]

theorem onceKernel_of_single_active (E : Finset (Finset ι)) (e : Finset ι) (v : Configuration ι)
    (h : activeEdges E v = {e}) : onceKernel E v = ofFinite (atom (deleteEdge e v)) := by
  simp [onceKernel, h, PositionalUniformAtoms.average]

theorem onceKernel_inserted_pair (E : Finset (Finset ι)) (e : Finset ι) (v : Configuration ι)
    (he : e ∈ E) (hE : ∀ f ∈ E, f.card = 2)
    (hno : activeEdges E v = ∅) (hz : ∀ x ∈ touchingVertices E e, v x = 0) :
    onceKernel E (v + edgeVector e) = ofFinite (atom v) := by
  rw [onceKernel_of_single_active E e _ (active_inserted_pair E e v he hE hno hz), delete_inserted]

theorem isolate_inserted_pair (E : Finset (Finset ι)) (e : Finset ι) (v : Configuration ι)
    (he : e ∈ E) (hE : ∀ f ∈ E, f.card = 2)
    (hno : activeEdges E v = ∅) (hz : ∀ x ∈ touchingVertices E e, v x = 0) :
    isolate E (v + edgeVector e) = v := by
  have heNonempty : e.Nonempty := card_pos.mp (by rw [hE e he]; omega)
  have hvertices : vertices E (v + edgeVector e) = e := by
    simp [vertices, active_inserted_pair E e v he hE hno hz]
  ext x
  rw [isolate, Finsupp.filter_apply, hvertices]
  by_cases hx : x ∈ e
  · rw [ite_eq_right (not_not.mpr hx), hz x (edge_subset_touching E e he heNonempty hx)]
  · rw [ite_eq_left hx, Finsupp.add_apply, edgeVector_apply, ite_eq_right hx, add_zero]

end PaperP1.PositionalInsertedPair
