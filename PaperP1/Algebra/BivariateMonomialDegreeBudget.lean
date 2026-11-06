module

public import PaperP1.Algebra.CountingWeightBudget
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Sum

/-! # The exact degree-sum budget for arbitrary distinct monomials in two free parameters -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateMonomialDegreeBudget

open Finset

def monomials (L : ℕ) : Finset (ℕ × ℕ) := (range L).biUnion fun r ↦ antidiagonal r

theorem mem_monomials (L : ℕ) (u : ℕ × ℕ) : u ∈ monomials L ↔ u.1 + u.2 < L := by
  simp only [monomials, mem_biUnion, mem_range, mem_antidiagonal]
  constructor
  · rintro ⟨r, hr, he⟩
    exact he.symm ▸ hr
  · intro hu
    exact ⟨u.1 + u.2, hu, rfl⟩

theorem card_monomials (L : ℕ) : (monomials L).card = (L + 1).choose 2 := by
  have hd : (range L : Set ℕ).PairwiseDisjoint (fun r ↦ (antidiagonal r : Finset (ℕ × ℕ))) := by
    intro r _hr s _hs hrs
    apply Finset.disjoint_left.mpr
    intro u hur hus
    exact hrs ((mem_antidiagonal.mp hur).symm.trans (mem_antidiagonal.mp hus))
  rw [monomials, Finset.card_biUnion hd]
  simp only [Finset.Nat.card_antidiagonal]
  cases L with
  | zero => simp
  | succ L => simpa using Nat.sum_range_add_choose L 1

theorem count_degree_le {ι : Type*} [Fintype ι] (f : ι → ℕ × ℕ) (hf : Function.Injective f) (r : ℕ) :
    ((univ : Finset ι).filter fun i ↦ (f i).1 + (f i).2 ≤ r).card ≤ (r + 2).choose 2 := by
  classical
  rw [← card_monomials (r + 1)]
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact (mem_monomials _ _).mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2)
  · intro i _hi j _hj he
    exact hf he

theorem sum_choose_two (L : ℕ) : (∑ r ∈ range L, (r + 2).choose 2) = (L + 2).choose 3 := by
  cases L with
  | zero => simp
  | succ L => simpa [Nat.add_assoc] using Nat.sum_range_add_choose L 2

theorem total_degree_budget {ι : Type*} [Fintype ι] (f : ι → ℕ × ℕ) (hf : Function.Injective f) (L : ℕ) :
    L * Fintype.card ι ≤ (∑ i, ((f i).1 + (f i).2)) + (L + 2).choose 3 := by
  have hh := CountingWeightBudget.layer_budget (fun i ↦ (f i).1 + (f i).2) L
  apply hh.trans
  apply Nat.add_le_add_left
  rw [← sum_choose_two]
  exact Finset.sum_le_sum (fun r _ ↦ count_degree_le f hf r)

end PaperP1.BivariateMonomialDegreeBudget
