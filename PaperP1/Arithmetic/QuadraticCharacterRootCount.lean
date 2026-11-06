module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-! # Exact counts of independent square-root choices, including zero radicands -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticCharacterRootCount

open Finset
open scoped Classical

variable {F ι : Type*} [Field F] [Fintype F] [Fintype ι]

def roots (r : ι → F) : Finset (ι → F) := univ.filter (fun z ↦ ∀ i, z i ^ 2 = r i)

theorem scalar_cardinality (hodd : ringChar F ≠ 2) (r : F) :
    (Fintype.card {z : F // z ^ 2 = r} : ℤ) = 1 + quadraticChar F r := by
  have he : Fintype.card {z : F // z ^ 2 = r} = ({z : F | z ^ 2 = r} : Set F).toFinset.card := by
    exact Fintype.card_of_finset' (p := {z : F | z ^ 2 = r}) _ (fun z ↦ Set.mem_toFinset)
  rw [he]
  simpa only [add_comm] using quadraticChar_card_sqrts hodd r

theorem cardinality (hodd : ringChar F ≠ 2) (r : ι → F) :
    ((roots r).card : ℤ) = ∏ i, (1 + quadraticChar F (r i)) := by
  have hc : (roots r).card = Fintype.card {z : ι → F // ∀ i, z i ^ 2 = r i} := by
    symm
    exact Fintype.card_of_finset' (p := {z : ι → F | ∀ i, z i ^ 2 = r i}) (roots r)
      (fun z ↦ by simp only [roots, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq])
  let e : {z : ι → F // ∀ i, z i ^ 2 = r i} ≃ (∀ i, {z : F // z ^ 2 = r i}) :=
    { toFun := fun z i ↦ ⟨z.val i, z.property i⟩
      invFun := fun z ↦ ⟨fun i ↦ (z i).val, fun i ↦ (z i).property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [hc, Fintype.card_congr e, Fintype.card_pi, Nat.cast_prod]
  exact prod_congr rfl (fun i _ ↦ scalar_cardinality hodd (r i))

theorem quadratic_character_bounds (r : F) : -1 ≤ quadraticChar F r ∧ quadraticChar F r ≤ 1 := by
  by_cases hr : r = 0
  · simp only [hr, quadraticChar_zero]; omega
  · rcases quadraticChar_dichotomy hr with h | h <;> rw [h] <;> omega

theorem quadratic_character_abs_le_one (r : F) : |(quadraticChar F r : ℝ)| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := quadratic_character_bounds r
  apply abs_le.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

end PaperP1.QuadraticCharacterRootCount
