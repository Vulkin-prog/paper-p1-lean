module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-! # Counting an actual finite cover from the actual cardinalities of its members -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCoverCount

open Finset

theorem cardinal_le {α ι : Type*} (S : Finset α) (I : Finset ι) (F : ι → Finset α) (A : ℝ)
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ F i)
    (hF : ∀ i ∈ I, ((F i).card : ℝ) ≤ A) : (S.card : ℝ) ≤ (I.card : ℝ) * A := by
  classical
  have hsub : S ⊆ I.biUnion F := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcover x hx
    exact mem_biUnion.mpr ⟨i, hi, hxi⟩
  calc
    (S.card : ℝ) ≤ ((I.biUnion F).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ((∑ i ∈ I, (F i).card : ℕ) : ℝ) := by exact_mod_cast (card_biUnion_le : (I.biUnion F).card ≤ _)
    _ = ∑ i ∈ I, ((F i).card : ℝ) := by rw [Nat.cast_sum]
    _ ≤ ∑ _i ∈ I, A := sum_le_sum hF
    _ = _ := by simp

end PaperP1.FiniteCoverCount
