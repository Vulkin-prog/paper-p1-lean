module

public import PaperP1.Model.RelativeWindowFamilies
public import PaperP1.Affine.MissingBlockRelations

/-! # Adjoining relative participating targets to participating sources preserves participation at every original coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeParticipatingUnion

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.RelativeWindowFamilies

local instance relativeParticipatingUnionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance (S : Submodule F₂ (ℕ →₀ F₂)) : AddCommGroup S :=
  Submodule.addCommGroup (R := F₂) (M := ℕ →₀ F₂) S

local instance (S : Submodule F₂ (ℕ →₀ F₂)) : Module F₂ S := S.module

theorem union_witnesses (L : ℕ) (e A : Finset ℕ) (he : Witnesses L ⊥ e)
    (hA : Witnesses L (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) A) :
    Witnesses L ⊥ (e ∪ A) := by
  classical
  let S := fun x ↦ squareClassSpace x L
  intro i
  by_cases hie : i.val ∈ e
  · obtain ⟨u, hu, hsum⟩ := he ⟨i.val, hie⟩
    let v := subfamilyExtend S (subset_union_left : e ⊆ e ∪ A) u
    refine ⟨v, ?_, ?_⟩
    · change (if hi : i.val ∈ e then u ⟨i.val, hi⟩ else (0 : S i.val)) ≠ 0
      simpa only [dite_eq_left hie] using hu
    · have hs : relationAddition (fun j : (e ∪ A : Finset ℕ) ↦ S j.val) v = 0 := by
        rw [relationAddition_subfamilyExtend]
        simpa only [relationAddition_apply, Submodule.mem_bot] using hsum
      simpa only [relationAddition_apply, Submodule.mem_bot] using hs
  · have hiA : i.val ∈ A := (mem_union.mp i.property).resolve_left hie
    obtain ⟨u, hu, hsum⟩ := hA ⟨i.val, hiA⟩
    change (∑ j : A, (u j).val) ∈ ⨆ j : e, S j.val at hsum
    rw [← range_relationAddition (fun j : e ↦ S j.val)] at hsum
    obtain ⟨t, ht⟩ := hsum
    let v := subfamilyExtend S (subset_union_right : A ⊆ e ∪ A) u -
      subfamilyExtend S (subset_union_left : e ⊆ e ∪ A) t
    refine ⟨v, ?_, ?_⟩
    · change ((if hi : i.val ∈ A then u ⟨i.val, hi⟩ else (0 : S i.val)) -
        (if hi : i.val ∈ e then t ⟨i.val, hi⟩ else (0 : S i.val))) ≠ 0
      simpa only [dite_eq_left hiA, dite_eq_right hie, sub_zero] using hu
    · have hs : relationAddition (fun j : (e ∪ A : Finset ℕ) ↦ S j.val) v = 0 := by
        dsimp only [v]
        rw [map_sub, relationAddition_subfamilyExtend, relationAddition_subfamilyExtend, ht,
          relationAddition_apply, sub_self]
      simpa only [relationAddition_apply, Submodule.mem_bot] using hs

theorem pair_witnesses (L : ℕ) (e : Finset ℕ) (hcard : e.card = 2)
    (hpos : 0 < relativeNullityOn (fun x ↦ squareClassSpace x L) e) : Witnesses L ⊥ e := by
  obtain ⟨u, hfull, hsum⟩ := PrimitiveRelations.full_relation_of_minimal_nullity
    (fun x ↦ squareClassSpace x L) e hpos (by
      intro J hJ
      have hle : J.card ≤ 1 := by have h := card_lt_card hJ; omega
      exact RetainedNullity.nullity_card_le_one _ J hle)
  exact fun i ↦ ⟨u, hfull i, by simpa only [relationAddition_apply, Submodule.mem_bot] using hsum⟩

end PaperP1.RelativeParticipatingUnion
