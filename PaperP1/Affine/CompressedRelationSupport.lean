module

public import PaperP1.Affine.RetainedDependence
public import PaperP1.Affine.MissingBlockRelations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Equal compressed nullity forces every actual relation to stay inside the pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedRelationSupport

open Finset PaperP1.Affine PaperP1.RetainedDependence

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem kernel_extension_surjective {e I : Finset κ} (heI : e ⊆ I)
    (heq : relativeNullityOn S I = relativeNullityOn S e) :
    Function.Surjective (subfamilyKernelExtend S heI) := by
  have hdim : Module.finrank 𝔽₂ (RelationOn S e) = Module.finrank 𝔽₂ (RelationOn S I) := heq.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (subfamilyKernelExtend_injective S heI)

theorem relation_zero_outside {e I : Finset κ} (heI : e ⊆ I)
    (heq : relativeNullityOn S I = relativeNullityOn S e)
    (w : (i : I) → S i.val) (hw : relationAddition (fun i : I ↦ S i.val) w = 0)
    (i : I) (hi : i.val ∉ e) : w i = 0 := by
  obtain ⟨v, hv⟩ := kernel_extension_surjective S heI heq (⟨w, hw⟩ : RelationOn S I)
  have he := congrFun (congrArg Subtype.val hv) i
  change (if h : i.val ∈ e then v.val ⟨i.val, h⟩ else 0) = w i at he
  simpa only [hi, dite_false] using he.symm

theorem no_full_support_of_proper {e I : Finset κ} (heI : e ⊆ I) (hne : e ≠ I)
    (heq : relativeNullityOn S I = relativeNullityOn S e) :
    ¬ ∃ w, IsFullSupportRelation (fun i : I ↦ S i.val) w := by
  intro ⟨w, hw⟩
  have hnot : ¬ I ⊆ e := fun h ↦ hne (Subset.antisymm heI h)
  obtain ⟨i, hiI, hie⟩ := Finset.not_subset.mp hnot
  exact hw.1 ⟨i, hiI⟩ (relation_zero_outside S heI heq w hw.2 ⟨i, hiI⟩ hie)

theorem no_full_support_of_nullity_zero (I : Finset κ) (hne : I.Nonempty)
    (hzero : relativeNullityOn S I = 0) :
    ¬ ∃ w, IsFullSupportRelation (fun i : I ↦ S i.val) w := by
  apply no_full_support_of_proper S (empty_subset I) (Ne.symm hne.ne_empty)
  rw [hzero, relativeNullityOn_empty]

theorem no_full_support_retained_large (E : Finset (Finset κ)) (hE : ∀ e ∈ E, e.card = 2)
    (I : Finset κ) (hI : Retained S E I) (hlarge : 3 ≤ I.card) :
    ¬ ∃ w, IsFullSupportRelation (fun i : I ↦ S i.val) w := by
  rcases hI with hzero | ⟨e, he, hcomp⟩
  · exact no_full_support_of_nullity_zero S I (card_pos.mp (by omega)) hzero
  · apply no_full_support_of_proper S hcomp.1 _ hcomp.2
    intro heq
    have hcard := hE e he
    rw [heq] at hcard
    omega

theorem no_full_support_restriction_except_pair (e I : Finset κ) (he : e.card = 2)
    (hcomp : Compressed S e I) (J : Finset κ) (hJI : J ⊆ I) (hJ : J.Nonempty) (hne : J ≠ e) :
    ¬ ∃ w, IsFullSupportRelation (fun j : J ↦ S j.val) w := by
  rcases compressed_subfamily S e I J he hcomp hJI with hzero | hcompressed
  · exact no_full_support_of_nullity_zero S J hJ hzero
  · exact no_full_support_of_proper S hcompressed.1 hne.symm hcompressed.2

end PaperP1.CompressedRelationSupport
