module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-! # A finite layer count bounds the sum of actual nonnegative weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CountingWeightBudget

open Finset

theorem one_weight (L w : ℕ) : L ≤ w + ((range L).filter fun r ↦ w ≤ r).card := by
  have hsub : (range L).filter (fun r ↦ r < w) ⊆ range w := by
    intro r hr
    exact mem_range.mpr (mem_filter.mp hr).2
  have hcard : ((range L).filter fun r ↦ r < w).card ≤ w := by
    simpa only [card_range] using card_le_card hsub
  have hsplit := card_filter_add_card_filter_not (s := range L) (fun r ↦ r < w)
  simp only [not_lt, card_range] at hsplit
  omega

theorem layer_budget {ι : Type*} [Fintype ι] (w : ι → ℕ) (L : ℕ) :
    L * Fintype.card ι ≤ (∑ i, w i) + ∑ r ∈ range L, ((univ : Finset ι).filter fun i ↦ w i ≤ r).card := by
  classical
  have hs := Finset.sum_le_sum (s := (univ : Finset ι)) (fun i _ ↦ one_weight L (w i))
  have hswap : (∑ i, ((range L).filter fun r ↦ w i ≤ r).card) =
      ∑ r ∈ range L, ((univ : Finset ι).filter fun i ↦ w i ≤ r).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ] at hs
  change Fintype.card ι * L ≤ _ at hs
  rw [hswap] at hs
  simpa only [Nat.mul_comm] using hs

end PaperP1.CountingWeightBudget
