module

public import PaperP1.Affine.PrivateNullity
public import PaperP1.Affine.CompatibleNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Supermodularity and restrictions of a single compressed dependence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedNullity

open Finset PaperP1.SubspaceFamilyRank PaperP1.Affine

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

local instance finite_span (A : Finset ι) : FiniteDimensional 𝔽₂ (span S A) := by
  have : ∀ i : A, FiniteDimensional 𝔽₂ (S i.val) := fun _ ↦ Module.Finite.of_finite
  exact Submodule.finiteDimensional_iSup (fun i : A ↦ S i.val)

omit [DecidableEq ι] in
theorem span_finite (A : Finset ι) : FiniteDimensional 𝔽₂ (span S A) := finite_span S A

omit [∀ i, Fintype (S i)] in
theorem span_union (A B : Finset ι) : span S (A ∪ B) = span S A ⊔ span S B := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    rcases mem_union.mp i.property with h | h
    · exact le_sup_of_le_left (local_le_span S A h)
    · exact le_sup_of_le_right (local_le_span S B h)
  · exact sup_le (span_mono S subset_union_left) (span_mono S subset_union_right)

omit [∀ i, Fintype (S i)] in
theorem span_inter_le (A B : Finset ι) : span S (A ∩ B) ≤ span S A ⊓ span S B :=
  le_inf (span_mono S inter_subset_left) (span_mono S inter_subset_right)

theorem rank_submodular (A B : Finset ι) :
    rank S (A ∪ B) + rank S (A ∩ B) ≤ rank S A + rank S B := by
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span S A) (span S B)
  have hinter := Submodule.finrank_mono (span_inter_le S A B)
  change rank S (A ∩ B) ≤ Module.finrank 𝔽₂ ↥(span S A ⊓ span S B) at hinter
  have hunion : rank S (A ∪ B) = Module.finrank 𝔽₂ ↥(span S A ⊔ span S B) := by
    rw [rank, span_union]
  change Module.finrank 𝔽₂ ↥(span S A ⊔ span S B) + Module.finrank 𝔽₂ ↥(span S A ⊓ span S B) =
    rank S A + rank S B at hmod
  omega

theorem nullity_supermodular (A B : Finset ι) :
    relativeNullityOn S A + relativeNullityOn S B ≤
      relativeNullityOn S (A ∪ B) + relativeNullityOn S (A ∩ B) := by
  have hA := rank_add_nullity_on S A
  have hB := rank_add_nullity_on S B
  have hUnion := rank_add_nullity_on S (A ∪ B)
  have hInter := rank_add_nullity_on S (A ∩ B)
  have hrank := rank_submodular S A B
  have hsum := (sum_union_inter :
    (∑ i ∈ A ∪ B, Module.finrank 𝔽₂ (S i)) + ∑ i ∈ A ∩ B, Module.finrank 𝔽₂ (S i) =
      (∑ i ∈ A, Module.finrank 𝔽₂ (S i)) + ∑ i ∈ B, Module.finrank 𝔽₂ (S i))
  omega

omit [DecidableEq ι] in
theorem nullity_singleton (i : ι) : relativeNullityOn S {i} = 0 := by
  have h := rank_add_nullity_on S {i}
  have hspan : span S {i} = S i := by simp [span]
  simp only [sum_singleton] at h
  change Module.finrank 𝔽₂ (span S {i}) + relativeNullityOn S {i} = Module.finrank 𝔽₂ (S i) at h
  rw [hspan] at h
  omega

omit [DecidableEq ι] in
theorem nullity_card_le_one (A : Finset ι) (hA : A.card ≤ 1) : relativeNullityOn S A = 0 := by
  by_cases hne : A.Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hsingle : A = {i} := by
      ext j
      constructor
      · intro hj
        exact mem_singleton.mpr ((card_le_one.mp hA) j hj i hi)
      · intro hj
        simpa only [mem_singleton.mp hj] using hi
    rw [hsingle]
    exact nullity_singleton S i
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact relativeNullityOn_empty S

theorem compressed_restriction (e I J : Finset ι) (heI : e ⊆ I)
    (hJI : J ⊆ I) (hnull : relativeNullityOn S I = relativeNullityOn S e) :
    relativeNullityOn S J = relativeNullityOn S (J ∩ e) := by
  have hsuper := nullity_supermodular S J e
  have hupper := relativeNullityOn_mono S (union_subset hJI heI)
  have hlower := relativeNullityOn_mono S (show J ∩ e ⊆ J from inter_subset_left)
  omega

theorem nullity_insert_le (i : ι) (A : Finset ι) :
    relativeNullityOn S (insert i A) ≤ relativeNullityOn S A + Module.finrank 𝔽₂ (S i) := by
  by_cases hi : i ∈ A
  · rw [insert_eq_of_mem hi]
    omega
  · have hfull := rank_add_nullity_on S (insert i A)
    have hbase := rank_add_nullity_on S A
    have hmono := Submodule.finrank_mono (span_mono S (subset_insert i A))
    change rank S A ≤ rank S (insert i A) at hmono
    rw [sum_insert hi] at hfull
    omega

omit [∀ i, Fintype (S i)] in
theorem span_pair (x y : ι) : span S {x, y} = S x ⊔ S y := by
  rw [span_insert]
  simp [span]

theorem nullity_pair_eq_intersection (x y : ι) (hxy : x ≠ y) :
    relativeNullityOn S {x, y} = Module.finrank 𝔽₂ ↥(S x ⊓ S y) := by
  have h := rank_add_nullity_on S {x, y}
  rw [sum_pair hxy] at h
  change Module.finrank 𝔽₂ (span S {x, y}) + relativeNullityOn S {x, y} =
    Module.finrank 𝔽₂ (S x) + Module.finrank 𝔽₂ (S y) at h
  rw [span_pair] at h
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (S x) (S y)
  omega

end PaperP1.RetainedNullity
