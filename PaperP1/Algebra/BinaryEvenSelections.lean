module

public import PaperP1.Algebra.EvenSupportRank
public import PaperP1.Arithmetic.ParityVector
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Powerset

/-! # Even binary coefficient vectors and literal even selected subsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryEvenSelections

open Finset PaperP1.Arithmetic

local instance binaryEvenSelectionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

local instance : DecidableEq ι := Classical.decEq ι

def selected (w : ι → F₂) : Finset ι := univ.filter fun i ↦ w i ≠ 0

def coefficients (S : Finset ι) (i : ι) : F₂ := if i ∈ S then 1 else 0

theorem binary_bit (z : F₂) : z = 0 ∨ z = 1 := by revert z; decide

theorem selected_coefficients (S : Finset ι) : selected (coefficients S) = S := by
  ext i
  simp [selected, coefficients]

theorem coefficients_selected (w : ι → F₂) : coefficients (selected w) = w := by
  funext i
  rcases binary_bit (w i) with h | h <;> simp [coefficients, selected, h]

theorem weighted_selected_sum (w f : ι → F₂) :
    (∑ i, w i * f i) = ∑ i ∈ selected w, f i := by
  rw [selected, sum_filter]
  apply sum_congr rfl
  intro i _
  rcases binary_bit (w i) with h | h <;> simp [h]

theorem sum_selected_card (w : ι → F₂) : (∑ i, w i) = ((selected w).card : F₂) := by
  have h := weighted_selected_sum w (fun _ ↦ 1)
  simpa using h

theorem even_selected_iff (w : ι → F₂) :
    Even (selected w).card ↔ w ∈ LinearMap.ker (EvenSupportRank.sumMap F₂ ι) := by
  rw [LinearMap.mem_ker, EvenSupportRank.sumMap_apply, sum_selected_card,
    ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

def evenEquiv : LinearMap.ker (EvenSupportRank.sumMap F₂ ι) ≃ {S : Finset ι // Even S.card} where
  toFun w := ⟨selected w.val, (even_selected_iff _).mpr w.property⟩
  invFun S := ⟨coefficients S.val, (even_selected_iff _).mp (by rw [selected_coefficients]; exact S.property)⟩
  left_inv w := Subtype.ext (coefficients_selected w.val)
  right_inv S := Subtype.ext (selected_coefficients S.val)

theorem selected_nonempty_iff (w : ι → F₂) : (selected w).Nonempty ↔ w ≠ 0 := by
  constructor
  · rintro ⟨i, hi⟩ hz
    exact (mem_filter.mp hi).2 (congrFun hz i)
  · intro hn
    by_contra he
    apply hn
    funext i
    by_contra hi
    exact he ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩

theorem selected_card_two {w : LinearMap.ker (EvenSupportRank.sumMap F₂ ι)} (hw : w ≠ 0) :
    2 ≤ (selected w.val).card := by
  have hn : (selected w.val).Nonempty := (selected_nonempty_iff _).mpr (fun h ↦ hw (Subtype.ext h))
  have he := (even_selected_iff _).mpr w.property
  obtain ⟨k, hk⟩ := he
  have hp := card_pos.mpr hn
  omega

def nonemptyEvenEquiv :
    {w : LinearMap.ker (EvenSupportRank.sumMap F₂ ι) // w ≠ 0} ≃
      {S : Finset ι // S.Nonempty ∧ Even S.card} where
  toFun w := ⟨selected w.val.val,
    (selected_nonempty_iff _).mpr (fun h ↦ w.property (Subtype.ext h)),
    (even_selected_iff _).mpr w.val.property⟩
  invFun S := ⟨evenEquiv.symm ⟨S.val, S.property.2⟩, by
    intro h
    have hz : (evenEquiv.symm ⟨S.val, S.property.2⟩).val = 0 := congrArg Subtype.val h
    have hs : selected (evenEquiv.symm ⟨S.val, S.property.2⟩).val = S.val := selected_coefficients S.val
    exact ((selected_nonempty_iff _).mp (hs.symm ▸ S.property.1)) hz⟩
  left_inv w := by
    apply Subtype.ext
    exact Subtype.ext (coefficients_selected w.val.val)
  right_inv S := Subtype.ext (selected_coefficients S.val)

end PaperP1.BinaryEvenSelections
