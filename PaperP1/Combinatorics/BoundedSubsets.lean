module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-! # A polynomial bound for finite subsets of bounded cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedSubsets

open Finset

variable {V : Type*} [DecidableEq V]

def sets (U : Finset V) (K : ℕ) : Finset (Finset V) :=
  (range (K + 1)).biUnion fun j ↦ U.powersetCard j

theorem mem_sets (U C : Finset V) (K : ℕ) : C ∈ sets U K ↔ C ⊆ U ∧ C.card ≤ K := by
  simp only [sets, mem_biUnion, mem_range, mem_powersetCard]
  constructor
  · rintro ⟨j, hj, hCU, hcard⟩
    exact ⟨hCU, by omega⟩
  · rintro ⟨hCU, hcard⟩
    exact ⟨C.card, by omega, hCU, rfl⟩

theorem card_sets (U : Finset V) (K : ℕ) :
    (sets U K).card ≤ (K + 1) * (U.card + 1) ^ K := by
  calc
    _ ≤ ∑ j ∈ range (K + 1), (U.powersetCard j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ range (K + 1), (U.card + 1) ^ K := by
      apply sum_le_sum
      intro j hj
      rw [card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (by omega) j).trans
        (Nat.pow_le_pow_right (by omega) (by have h := mem_range.mp hj; omega)))
    _ = _ := by simp

end PaperP1.BoundedSubsets
