module

public import PaperP1.Affine.RetainedDependence
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The exact direct-sum meaning of a compressed relative-nullity equality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedBlocks

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

abbrev Index (e I : Finset ι) := Option {i // i ∈ I \ e}

def family (e I : Finset ι) : Index e I → Submodule 𝔽₂ U
  | none => span S e
  | some i => S i.val

local instance familyFintype (e I : Finset ι) (i : Index e I) : Fintype (family S e I i) := by
  classical
  cases i with
  | none =>
    change Fintype (span S e)
    unfold span
    rw [← range_relationAddition (fun i : e ↦ S i.val)]
    exact Fintype.ofSurjective (relationAddition (fun i : e ↦ S i.val)).rangeRestrict (by
      rintro ⟨z, ⟨w, hw⟩⟩
      exact ⟨w, Subtype.ext hw⟩)
  | some i => exact inferInstanceAs (Fintype (S i.val))

def Direct (e I : Finset ι) : Prop := Function.Injective (relationAddition (family S e I))

omit [∀ i, Fintype (S i)] in
theorem range_addition (e I : Finset ι) (heI : e ⊆ I) :
    LinearMap.range (relationAddition (family S e I)) = span S I := by
  rw [range_relationAddition]
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    cases i with
    | none => exact span_mono S heI
    | some j => exact local_le_span S I (mem_sdiff.mp j.property).1
  · refine iSup_le fun i ↦ ?_
    by_cases hie : i.val ∈ e
    · exact le_iSup_of_le none (local_le_span S e hie)
    · exact le_iSup_of_le (some (⟨i.val, mem_sdiff.mpr ⟨i.property, hie⟩⟩ : {i // i ∈ I \ e})) le_rfl

theorem nullity_identity (e I : Finset ι) (heI : e ⊆ I) :
    relativeNullity (family S e I) + relativeNullityOn S e = relativeNullityOn S I := by
  have hcomp := relativeNullity_dimension_identity (family S e I)
  rw [Fintype.sum_option] at hcomp
  have hsum : (∑ i : {i // i ∈ I \ e}, Module.finrank 𝔽₂ (S i.val)) =
      ∑ i ∈ I \ e, Module.finrank 𝔽₂ (S i) := sum_coe_sort (I \ e) (fun i : ι ↦ Module.finrank 𝔽₂ (S i))
  change rank S e + (∑ i : {i // i ∈ I \ e}, Module.finrank 𝔽₂ (S i.val)) =
    Module.finrank 𝔽₂ (⨆ i, family S e I i : Submodule 𝔽₂ U) + relativeNullity (family S e I) at hcomp
  rw [hsum, ← range_relationAddition, range_addition S e I heI] at hcomp
  change rank S e + (∑ i ∈ I \ e, Module.finrank 𝔽₂ (S i)) = rank S I + relativeNullity (family S e I) at hcomp
  have he := rank_add_nullity_on S e
  have hI := rank_add_nullity_on S I
  have htotal : (∑ i ∈ I \ e, Module.finrank 𝔽₂ (S i)) +
      ∑ i ∈ e, Module.finrank 𝔽₂ (S i) = ∑ i ∈ I, Module.finrank 𝔽₂ (S i) := sum_sdiff heI
  omega

theorem direct_iff_compressed (e I : Finset ι) (heI : e ⊆ I) :
    Direct S e I ↔ PaperP1.RetainedDependence.Compressed S e I := by
  have hidentity := nullity_identity S e I heI
  constructor
  · intro hinj
    have hker := LinearMap.ker_eq_bot.mpr hinj
    have hz : relativeNullity (family S e I) = 0 := by
      unfold relativeNullity
      rw [hker, finrank_bot]
    exact ⟨heI, by omega⟩
  · intro hcomp
    have hz : relativeNullity (family S e I) = 0 := by have := hcomp.2; omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

omit [DecidableEq ι] in
theorem direct_family_iff_zero_nullity (I : Finset ι) :
    Function.Injective (relationAddition (fun i : I ↦ S i.val)) ↔ relativeNullityOn S I = 0 := by
  constructor
  · intro hinj
    have hker := LinearMap.ker_eq_bot.mpr hinj
    change Module.finrank 𝔽₂ (LinearMap.ker (relationAddition (fun i : I ↦ S i.val))) = 0
    rw [hker, finrank_bot]
  · intro hzero
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)

def SourceRetained (E : Finset (Finset ι)) (I : Finset ι) : Prop :=
  Function.Injective (relationAddition (fun i : I ↦ S i.val)) ∨
    ∃ e ∈ E, e ⊆ I ∧ Direct S e I

theorem sourceRetained_iff (E : Finset (Finset ι)) (I : Finset ι) :
    SourceRetained S E I ↔ PaperP1.RetainedDependence.Retained S E I := by
  constructor
  · rintro (hzero | ⟨e, he, heI, hdirect⟩)
    · exact Or.inl ((direct_family_iff_zero_nullity S I).mp hzero)
    · exact Or.inr ⟨e, he, (direct_iff_compressed S e I heI).mp hdirect⟩
  · rintro (hzero | ⟨e, he, hcomp⟩)
    · exact Or.inl ((direct_family_iff_zero_nullity S I).mpr hzero)
    · exact Or.inr ⟨e, he, hcomp.1, (direct_iff_compressed S e I hcomp.1).mpr hcomp⟩

end PaperP1.CompressedBlocks
