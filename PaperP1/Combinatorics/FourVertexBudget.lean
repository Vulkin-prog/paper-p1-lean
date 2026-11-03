module

public import PaperP1.Arithmetic.MediumPrimeColumns

/-! # The exact four-vertex budget after accounting for two- and three-vertex blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourVertexBudget

open Finset

theorem budget {V J : Type*} (A : Finset V) (Q : Finset J) (blocks : J → Finset V)
    (hsub : ∀ j ∈ Q, blocks j ⊆ A)
    (hdisjoint : (↑Q : Set J).Pairwise (fun i j ↦ Disjoint (blocks i) (blocks j)))
    (hmin : ∀ j ∈ Q, 2 ≤ (blocks j).card) :
    4 * Q.card ≤ A.card + 2 * (Q.filter fun j ↦ (blocks j).card = 2).card +
      (Q.filter fun j ↦ (blocks j).card = 3).card := by
  classical
  have hsize : ∑ j ∈ Q, (blocks j).card ≤ A.card := by
    rw [← card_biUnion hdisjoint]
    exact card_le_card (biUnion_subset.mpr hsub)
  have hterm : ∀ j ∈ Q, 4 ≤ (blocks j).card +
      (if (blocks j).card = 2 then 2 else 0) + (if (blocks j).card = 3 then 1 else 0) := by
    intro j hj
    have hm := hmin j hj
    split_ifs <;> omega
  have hsum := sum_le_sum hterm
  have htwo : (∑ j ∈ Q, if (blocks j).card = 2 then 2 else 0) =
      2 * (Q.filter fun j ↦ (blocks j).card = 2).card := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hthree : (∑ j ∈ Q, if (blocks j).card = 3 then 1 else 0) =
      (Q.filter fun j ↦ (blocks j).card = 3).card := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
  rw [sum_add_distrib, sum_add_distrib, htwo, hthree] at hsum
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id] at hsum
  omega

end PaperP1.FourVertexBudget
