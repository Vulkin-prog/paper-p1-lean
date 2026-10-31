module

public import PaperP1.Affine.Subfamilies

/-! # Covering relations by the blocks they miss

If no relation meets every effective block, the addition kernel is covered
by extension-by-zero images of the one-block-deleted kernels. This gives
the exact cardinal, hence power-of-two nullity, inequality of T22.2.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset

local instance missingBlockPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

abbrev RelationOn (I : Finset κ) :=
  LinearMap.ker (relationAddition (fun i : I ↦ S i.val))

local instance missingBlockKernelFintype (I : Finset κ) : Fintype (RelationOn S I) :=
  Fintype.ofFinite _

omit [∀ i, Fintype (S i)] in
theorem subfamilyExtend_has_preimage {J I : Finset κ} (hJI : J ⊆ I)
    (w : (i : I) → S i.val) (hzero : ∀ i : I, i.val ∉ J → w i = 0) :
    ∃ v : (j : J) → S j.val, subfamilyExtend S hJI v = w := by
  let v : (j : J) → S j.val := fun j ↦ w ⟨j.val, hJI j.property⟩
  refine ⟨v, ?_⟩
  funext i
  change (if hi : i.val ∈ J then v ⟨i.val, hi⟩ else 0) = w i
  split_ifs with hi
  · rfl
  · exact (hzero i hi).symm

omit [∀ i, Fintype (S i)] in
theorem subfamilyKernelExtend_has_preimage {J I : Finset κ} (hJI : J ⊆ I)
    (w : RelationOn S I) (hzero : ∀ i : I, i.val ∉ J → w.val i = 0) :
    ∃ v : RelationOn S J, subfamilyKernelExtend S hJI v = w := by
  obtain ⟨v, hv⟩ := subfamilyExtend_has_preimage S hJI w.val hzero
  have hker : v ∈ RelationOn S J := by
    change relationAddition (fun j : J ↦ S j.val) v = 0
    rw [← relationAddition_subfamilyExtend S hJI, hv]
    exact w.property
  exact ⟨⟨v, hker⟩, Subtype.ext hv⟩

def erasedKernelToFull (I : Finset κ) :
    (Σ i : I, RelationOn S (I.erase i.val)) → RelationOn S I :=
  fun v ↦ subfamilyKernelExtend S (erase_subset v.1.val I) v.2

omit [∀ i, Fintype (S i)] in
theorem erasedKernelToFull_surjective (I : Finset κ)
    (hmiss : ¬∃ w, IsFullSupportRelation (fun i : I ↦ S i.val) w) :
    Function.Surjective (erasedKernelToFull S I) := by
  classical
  intro w
  have hzero : ∃ i : I, w.val i = 0 := by
    by_contra h
    push Not at h
    exact hmiss ⟨w.val, h, w.property⟩
  obtain ⟨i, hi⟩ := hzero
  have hz : ∀ j : I, j.val ∉ I.erase i.val → w.val j = 0 := by
    intro j hj
    have hji : j = i := by
      apply Subtype.ext
      by_contra hne
      exact hj (mem_erase.mpr ⟨hne, j.property⟩)
    subst j
    exact hi
  obtain ⟨v, hv⟩ := subfamilyKernelExtend_has_preimage S (erase_subset i.val I) w hz
  exact ⟨⟨i, v⟩, hv⟩

omit [DecidableEq κ] in
theorem card_relationOn (I : Finset κ) :
    Fintype.card (RelationOn S I) = 2 ^ relativeNullityOn S I :=
  card_eq_two_pow_finrank (V := RelationOn S I)

theorem missing_full_support_nullity_bound (I : Finset κ)
    (hmiss : ¬∃ w, IsFullSupportRelation (fun i : I ↦ S i.val) w) :
    2 ^ relativeNullityOn S I ≤ ∑ i ∈ I, 2 ^ relativeNullityOn S (I.erase i) := by
  have hcard := Fintype.card_le_of_surjective _ (erasedKernelToFull_surjective S I hmiss)
  rw [Fintype.card_sigma, card_relationOn] at hcard
  simp_rw [card_relationOn] at hcard
  rw [← sum_coe_sort I (fun i : κ ↦ 2 ^ relativeNullityOn S (I.erase i))]
  exact hcard

theorem missing_full_support_nullity_bound_real (I : Finset κ)
    (hmiss : ¬∃ w, IsFullSupportRelation (fun i : I ↦ S i.val) w) :
    (2 ^ relativeNullityOn S I : ℝ) ≤
      ∑ i ∈ I, (2 ^ relativeNullityOn S (I.erase i) : ℝ) := by
  exact_mod_cast missing_full_support_nullity_bound S I hmiss

end PaperP1.Affine
