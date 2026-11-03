module

public import PaperP1.Affine.ErasedNullityRelations

/-! # A minimal dependent target family above one prescribed effective space has a relation nonzero in every target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MinimalRelativeRelations

open Finset PaperP1.Affine

local instance minimalRelativePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]

def augmented (W : Submodule 𝔽₂ U) (S : κ → Submodule 𝔽₂ U) : Option κ → Submodule 𝔽₂ U
  | none => W
  | some i => S i

def indices (A : Finset κ) : Finset (Option κ) := insert none (A.image some)

local instance augmentedFintype (W : Submodule 𝔽₂ U) [Fintype W]
    (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (i : Option κ) : Fintype (augmented W S i) := by
  cases i with
  | none => exact inferInstanceAs (Fintype W)
  | some i => exact inferInstanceAs (Fintype (S i))

def nullity (W : Submodule 𝔽₂ U) (S : κ → Submodule 𝔽₂ U) (A : Finset κ) : ℕ :=
  relativeNullityOn (augmented W S) (indices A)

@[instance_reducible] def spanFintype (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (E : Finset κ) :
    Fintype (SubspaceFamilyRank.span S E) := by
  classical
  unfold SubspaceFamilyRank.span
  rw [← range_relationAddition (fun i : E ↦ S i.val)]
  exact Fintype.ofSurjective (relationAddition (fun i : E ↦ S i.val)).rangeRestrict (by
    rintro ⟨z, ⟨w, hw⟩⟩
    exact ⟨w, Subtype.ext hw⟩)

theorem indices_erase (A : Finset κ) (i : κ) : indices (A.erase i) = (indices A).erase (some i) := by
  ext j
  cases j <;> simp [indices]

theorem nullity_empty (W : Submodule 𝔽₂ U) [Fintype W]
    (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] : nullity W S ∅ = 0 := by
  change relativeNullityOn (augmented W S) (indices ∅) = 0
  rw [show indices (∅ : Finset κ) = {none} by simp [indices]]
  exact PaperP1.RetainedNullity.nullity_singleton (augmented W S) none

theorem dimension_identity (W : Submodule 𝔽₂ U) [Fintype W]
    (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (A : Finset κ) :
    Module.finrank 𝔽₂ ↥(W ⊔ SubspaceFamilyRank.span S A) + nullity W S A =
      Module.finrank 𝔽₂ W + ∑ i ∈ A, Module.finrank 𝔽₂ (S i) := by
  have hspan : SubspaceFamilyRank.span (augmented W S) (indices A) = W ⊔ SubspaceFamilyRank.span S A := by
    rw [indices, SubspaceFamilyRank.span_insert, SubspaceFamilyRank.span_image]
    rfl
  have hsum : (∑ i ∈ indices A, Module.finrank 𝔽₂ (augmented W S i)) =
      Module.finrank 𝔽₂ W + ∑ i ∈ A, Module.finrank 𝔽₂ (S i) := by
    rw [indices, sum_insert (by simp), sum_image (fun _ _ _ _ h ↦ Option.some.inj h)]
    rfl
  have h := rank_add_nullity_on (augmented W S) (indices A)
  rw [SubspaceFamilyRank.rank, hspan, hsum] at h
  exact h

theorem source_union_identity (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]
    (E A : Finset κ) (hEA : Disjoint E A) :
    relativeNullityOn S (E ∪ A) = relativeNullityOn S E + nullity (SubspaceFamilyRank.span S E) S A := by
  classical
  let : FiniteDimensional 𝔽₂ (SubspaceFamilyRank.span S E) := RetainedNullity.span_finite S E
  let : Fintype (SubspaceFamilyRank.span S E) := spanFintype S E
  have hrel := dimension_identity (SubspaceFamilyRank.span S E) S A
  have hsource := rank_add_nullity_on S E
  have hfull := rank_add_nullity_on S (E ∪ A)
  rw [sum_union hEA, SubspaceFamilyRank.rank, RetainedNullity.span_union] at hfull
  change Module.finrank 𝔽₂ (SubspaceFamilyRank.span S E) + relativeNullityOn S E = _ at hsource
  omega

theorem zero_iff_compressed (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]
    (E A : Finset κ) (hEA : Disjoint E A) :
    nullity (SubspaceFamilyRank.span S E) S A = 0 ↔ RetainedDependence.Compressed S E (E ∪ A) := by
  have h := source_union_identity S E A hEA
  constructor
  · intro hz
    exact ⟨subset_union_left, by omega⟩
  · intro hc
    have heq := hc.2
    omega

theorem exists_minimal (W : Submodule 𝔽₂ U) [Fintype W]
    (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (I : Finset κ) (hpositive : 0 < nullity W S I) :
    ∃ A ⊆ I, A.Nonempty ∧ 0 < nullity W S A ∧ ∀ B : Finset κ, B ⊂ A → nullity W S B = 0 := by
  classical
  let P := I.powerset.filter fun A ↦ 0 < nullity W S A
  have hIP : I ∈ P := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, hpositive⟩
  obtain ⟨A, hAP, hmin⟩ := exists_min_image P Finset.card ⟨I, hIP⟩
  obtain ⟨hAI, hApos⟩ := mem_filter.mp hAP
  have hsub : A ⊆ I := mem_powerset.mp hAI
  have hne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, nullity_empty] at hApos
    omega
  refine ⟨A, hsub, hne, hApos, ?_⟩
  intro B hBA
  by_contra hB
  have hBP : B ∈ P := mem_filter.mpr ⟨mem_powerset.mpr (hBA.subset.trans hsub), Nat.pos_of_ne_zero hB⟩
  have hle := hmin B hBP
  have hlt := card_lt_card hBA
  omega

theorem exists_relation (W : Submodule 𝔽₂ U) [Fintype W]
    (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (A : Finset κ)
    (hpositive : 0 < nullity W S A) (hproper : ∀ B : Finset κ, B ⊂ A → nullity W S B = 0) :
    ∃ u : (i : A) → S i.val, (∀ i, u i ≠ 0) ∧ (∑ i : A, (u i).val) ∈ W := by
  obtain ⟨r, hrsum, hrnonzero⟩ := ErasedNullityRelations.relation_nonzero_on (augmented W S)
    (indices A) (A.image some) hpositive (by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
      rw [← indices_erase]
      exact hproper (A.erase i) (erase_ssubset hi))
  let f : Option κ → U := fun i ↦ if hi : i ∈ indices A then (r ⟨i, hi⟩).val else 0
  have hfi (i : Option κ) (hi : i ∈ indices A) : f i = (r ⟨i, hi⟩).val := dite_eq_left hi
  have hmem (i : A) : some i.val ∈ indices A :=
    mem_insert_of_mem (mem_image.mpr ⟨i.val, i.property, rfl⟩)
  let u : (i : A) → S i.val := fun i ↦ r ⟨some i.val, hmem i⟩
  have hfull : (∑ i ∈ indices A, f i) = 0 := by
    calc
      _ = ∑ i : indices A, f i.val := (sum_finset_subtype (indices A) f).symm
      _ = ∑ i : indices A, (r i).val := sum_congr rfl (fun i _ ↦ hfi i.val i.property)
      _ = 0 := hrsum
  rw [indices, sum_insert (by simp), sum_image (fun _ _ _ _ h ↦ Option.some.inj h)] at hfull
  have hsum : (∑ i : A, (u i).val) = ∑ i ∈ A, f (some i) := by
    rw [← sum_finset_subtype A (fun i ↦ f (some i))]
    exact sum_congr rfl (fun i _ ↦ (hfi (some i.val) (hmem i)).symm)
  refine ⟨u, ?_, ?_⟩
  · intro i
    exact hrnonzero ⟨some i.val, hmem i⟩ (mem_image.mpr ⟨i.val, i.property, rfl⟩)
  · rw [hsum, eq_neg_of_add_eq_zero_right hfull, hfi none (mem_insert_self _ _)]
    exact W.neg_mem (r ⟨none, mem_insert_self _ _⟩).property

end PaperP1.MinimalRelativeRelations
