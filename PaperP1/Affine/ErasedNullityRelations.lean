module

public import PaperP1.Affine.CompressedBlocks

/-! # Zero nullity after each designated deletion forces an actual relation nonzero at every designated coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ErasedNullityRelations

open Finset PaperP1.Affine

local instance erasedNullityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]

theorem relation_nonzero_on (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]
    (I A : Finset κ) (hpositive : 0 < relativeNullityOn S I)
    (hzero : ∀ i ∈ A, relativeNullityOn S (I.erase i) = 0) :
    ∃ s : (i : I) → S i.val, (∑ i : I, (s i).val) = 0 ∧ ∀ i : I, i.val ∈ A → s i ≠ 0 := by
  classical
  let T := fun i : I ↦ S i.val
  have hker : LinearMap.ker (relationAddition T) ≠ ⊥ := by
    intro hbot
    have hzero : relativeNullityOn S I = 0 := by
      change Module.finrank 𝔽₂ (LinearMap.ker (relationAddition T)) = 0
      rw [hbot, finrank_bot]
    omega
  obtain ⟨s, hs, hne⟩ := (Submodule.ne_bot_iff _).mp hker
  have hs0 : relationAddition T s = 0 := LinearMap.mem_ker.mp hs
  refine ⟨s, hs0, ?_⟩
  intro i hiA hsi
  let J := I.erase i.val
  have hJI : J ⊆ I := erase_subset _ _
  let w : (j : J) → S j.val := fun j ↦ s ⟨j.val, hJI j.property⟩
  have hext : subfamilyExtend S hJI w = s := by
    funext j
    by_cases hji : j.val = i.val
    · have hji' : j = i := Subtype.ext hji
      subst j
      have hiJ : i.val ∉ J := by simp [J]
      change (if h : i.val ∈ J then w ⟨i.val, h⟩ else 0) = s i
      rw [dite_eq_right hiJ]
      exact hsi.symm
    · have hjJ : j.val ∈ J := mem_erase.mpr ⟨hji, j.property⟩
      change (if h : j.val ∈ J then w ⟨j.val, h⟩ else 0) = s j
      rw [dite_eq_left hjJ]
  have hrestricted : relationAddition (fun j : J ↦ S j.val) w = 0 := by
    have hsum := relationAddition_subfamilyExtend S hJI w
    rw [hext] at hsum
    exact hsum.symm.trans hs0
  have hinj := (PaperP1.CompressedBlocks.direct_family_iff_zero_nullity S J).mpr (hzero i.val hiA)
  have hwzero : w = 0 := hinj (hrestricted.trans (map_zero _).symm)
  apply hne
  rw [← hext, hwzero, map_zero]

end PaperP1.ErasedNullityRelations
