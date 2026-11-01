module

public import PaperP1.Affine.PrivateNullity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! # Counting full-support relations by the exact one-coordinate deletion losses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

local instance fullRelationFintype (A : Finset ι) : Fintype (RelationOn S A) := Fintype.ofFinite _
local instance fullRelationDecidableEq (A : Finset ι) : DecidableEq (RelationOn S A) := Classical.decEq _
local instance fullTupleDecidableEq (A : Finset ι) : DecidableEq ((i : A) → S i.val) := Classical.decEq _

def fullRelations (A : Finset ι) : Finset (RelationOn S A) := by
  classical
  exact univ.filter fun w ↦ HasFullSupport (fun i : A ↦ S i.val) w.val

omit [FiniteDimensional 𝔽₂ U] in
theorem fullRelations_image (A : Finset ι) :
    (fullRelations S A).image Subtype.val = fullSupportRelations (fun i : A ↦ S i.val) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2, v.property⟩
  · intro hw
    obtain ⟨hsupport, hzero⟩ := (mem_filter.mp hw).2
    exact mem_image.mpr ⟨⟨w, hzero⟩, mem_filter.mpr ⟨mem_univ _, hsupport⟩, rfl⟩

omit [FiniteDimensional 𝔽₂ U] in
theorem fullRelations_card (A : Finset ι) :
    (fullRelations S A).card = (fullSupportRelations (fun i : A ↦ S i.val)).card := by
  rw [← fullRelations_image S A, card_image_of_injective _ Subtype.val_injective]

omit [FiniteDimensional 𝔽₂ U] in
theorem fullSupport_card_lower (A : Finset ι) :
    2 ^ relativeNullityOn S A ≤ (fullSupportRelations (fun i : A ↦ S i.val)).card +
      ∑ i : A, 2 ^ relativeNullityOn S (A.erase i.val) := by
  classical
  let bad := univ.biUnion fun i : A ↦ missedRelations S A i
  have hcover : (univ : Finset (RelationOn S A)) ⊆ fullRelations S A ∪ bad := by
    intro w _
    by_cases hw : ∀ i : A, w.val i ≠ 0
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hw⟩)
    · push Not at hw
      obtain ⟨i, hi⟩ := hw
      exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩)
  have hbad : bad.card ≤ ∑ i : A, 2 ^ relativeNullityOn S (A.erase i.val) := by
    calc
      _ ≤ ∑ i : A, (missedRelations S A i).card := card_biUnion_le
      _ = _ := sum_congr rfl (fun i _ ↦ card_missedRelations S A i)
  have hcard := card_le_card hcover
  have hunion := card_union_le (fullRelations S A) bad
  rw [card_univ, card_relationOn] at hcard
  rw [fullRelations_card] at hunion
  omega

theorem missed_card_ratio (A : Finset ι) (i : A) :
    ((missedRelations S A i).card : ℝ) = (2 ^ relativeNullityOn S A : ℝ) *
      ((2 ^ privateRank S A i.val : ℝ) / (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ)) := by
  have hdim := private_nullity_identity S A i.property
  have hpow : (2 ^ relativeNullityOn S (A.erase i.val) : ℝ) * (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ) =
      (2 ^ relativeNullityOn S A : ℝ) * 2 ^ privateRank S A i.val := by
    rw [← pow_add, ← pow_add, hdim]
  rw [card_missedRelations, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_div_assoc]
  apply (eq_div_iff (by positivity : (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ) ≠ 0)).mpr
  exact hpow

theorem fullSupport_profile_lower (A : Finset ι) :
    (2 ^ relativeNullityOn S A : ℝ) *
      (1 - ∑ i : A, (2 ^ privateRank S A i.val : ℝ) / (2 ^ Module.finrank 𝔽₂ (S i.val) : ℝ)) ≤
        (fullSupportRelations (fun i : A ↦ S i.val)).card := by
  have hcard : (2 ^ relativeNullityOn S A : ℝ) ≤
      (fullSupportRelations (fun i : A ↦ S i.val)).card + ∑ i : A, ((missedRelations S A i).card : ℝ) := by
    have h := fullSupport_card_lower S A
    have hR : ((2 ^ relativeNullityOn S A : ℕ) : ℝ) ≤
        (fullSupportRelations (fun i : A ↦ S i.val)).card +
          ((∑ i : A, 2 ^ relativeNullityOn S (A.erase i.val) : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum, card_missedRelations,
      Nat.cast_pow, Nat.cast_ofNat] using hR
  simp_rw [missed_card_ratio S A] at hcard
  rw [← mul_sum] at hcard
  nlinarith

end PaperP1.Affine
