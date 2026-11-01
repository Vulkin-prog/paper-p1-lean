module

public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Data.Finset.Card

/-! # Exact finite cardinal bookkeeping for decreasing stages -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteStageCounts

open Finset

theorem initial_cover {α : Type*} [DecidableEq α] (S A B : Finset α) :
    S.card ≤ A.card + B.card + (S \ (A ∪ B)).card := by
  have hcover : S ⊆ (A ∪ B) ∪ (S \ (A ∪ B)) := by
    intro x hx
    by_cases h : x ∈ A ∪ B
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx, h⟩)
  exact (card_le_card hcover).trans ((card_union_le (s := A ∪ B) (t := S \ (A ∪ B))).trans
    (Nat.add_le_add_right (card_union_le (s := A) (t := B)) _))

theorem decreasing_identity {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (J : ℕ)
    (hS : ∀ j < J, S (j + 1) ⊆ S j) :
    (S 0).card = (S J).card + ∑ j ∈ range J, (S j \ S (j + 1)).card := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hprev := ih (fun j hj ↦ hS j (by omega))
    have hlast := card_sdiff_add_card_eq_card (hS J (by omega))
    rw [sum_range_succ]
    omega

theorem decreasing_bound {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (J : ℕ) (A B : ℝ)
    (hS : ∀ j < J, S (j + 1) ⊆ S j)
    (hlast : ((S J).card : ℝ) ≤ A)
    (hremoved : ∀ j < J, ((S j \ S (j + 1)).card : ℝ) ≤ B) :
    ((S 0).card : ℝ) ≤ A + (J : ℝ) * B := by
  rw [decreasing_identity S J hS, Nat.cast_add, Nat.cast_sum]
  have hs : (∑ j ∈ range J, ((S j \ S (j + 1)).card : ℝ)) ≤ (J : ℝ) * B := by
    calc
      _ ≤ ∑ _j ∈ range J, B := sum_le_sum (fun j hj ↦ hremoved j (mem_range.mp hj))
      _ = _ := by simp
  exact add_le_add hlast hs

end PaperP1.FiniteStageCounts
