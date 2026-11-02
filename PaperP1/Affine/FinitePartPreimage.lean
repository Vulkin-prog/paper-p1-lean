module

public import PaperP1.Affine.FinitePartImage
public import PaperP1.Algebra.SubspaceFamilyRank

/-! # Exact restriction of an original subset to a finite subtype -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePartPreimage

open Finset PaperP1.SubspaceFamilyRank PaperP1.Affine

variable {κ : Type*} [DecidableEq κ]

def part (I A : Finset κ) : Finset I := univ.filter (fun i ↦ i.val ∈ A)

theorem image_part (I A : Finset κ) (hAI : A ⊆ I) :
    FinitePartImage.image (part I A) = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hi).2
  · intro hx
    exact mem_image.mpr ⟨⟨x, hAI hx⟩, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩

theorem part_nonempty (I A : Finset κ) (hAI : A ⊆ I) (hA : A.Nonempty) :
    (part I A).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  exact ⟨⟨x, hAI hx⟩, mem_filter.mpr ⟨mem_univ _, hx⟩⟩

theorem parts_disjoint (I A B : Finset κ) (hAB : Disjoint A B) :
    Disjoint (part I A) (part I B) := by
  apply disjoint_left.mpr
  intro i hiA hiB
  exact disjoint_left.mp hAB (mem_filter.mp hiA).2 (mem_filter.mp hiB).2

theorem parts_union (I A B : Finset κ) (hcover : A ∪ B = I) :
    part I A ∪ part I B = univ := by
  ext i
  constructor
  · intro _
    exact mem_univ _
  · intro _
    have hi : i.val ∈ A ∪ B := hcover.symm ▸ i.property
    rcases mem_union.mp hi with hA | hB
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hA⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hB⟩)

variable {U : Type*} [AddCommGroup U] [Module 𝔽₂ U]

theorem span_image (S : κ → Submodule 𝔽₂ U) {I : Finset κ} (C : Finset I) :
    span (fun i : I ↦ S i.val) C = span S (FinitePartImage.image C) := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    exact le_iSup_of_le (⟨i.val.val, mem_image.mpr ⟨i.val, i.property, rfl⟩⟩ : FinitePartImage.image C) le_rfl
  · refine iSup_le fun k ↦ ?_
    obtain ⟨i, hi, hik⟩ := mem_image.mp k.property
    change S k.val ≤ span (fun i : I ↦ S i.val) C
    rw [← hik]
    exact le_iSup_of_le (⟨i, hi⟩ : C) le_rfl

end PaperP1.FinitePartPreimage
