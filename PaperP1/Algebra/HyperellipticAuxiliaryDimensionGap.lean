module

public import PaperP1.Algebra.HyperellipticMonomialIndex
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-! # A literal large-prime threshold proves the actual auxiliary dimension inequality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticAuxiliaryDimensionGap

open Finset HyperellipticMonomialIndex

theorem dimension_gap (g m p : ℕ) (hm : g + 1 ≤ m) (hpd : 2 * g + 2 ≤ p)
    (hlarge : g + m * (m + g) + m * (m - 1) * ((2 * g + 1) - 2) + 1 ≤ p) :
    (∑ r : Fin m, Fintype.card (Index (2 * g + 1)
      ((p - 1) + (m + g) + r.val * ((2 * g + 1) - 2)))) <
      Fintype.card (Index (2 * g + 1) (p - 1)) * Fintype.card (Index (2 * g + 1) (m + g)) := by
  have hA : 2 * g + 1 ≤ p - 1 := by omega
  have hB : 2 * g + 1 ≤ m + g := by omega
  have hentry (r : Fin m) : Fintype.card (Index (2 * g + 1)
      ((p - 1) + (m + g) + r.val * ((2 * g + 1) - 2))) ≤
      ((p - 1) + 1 - g) + (m + g) + (m - 1) * ((2 * g + 1) - 2) := by
    have hcap : 2 * g + 1 ≤ (p - 1) + (m + g) + r.val * ((2 * g + 1) - 2) := by omega
    rw [cardinality_odd g _ hcap]
    have hr : r.val ≤ m - 1 := by have hh := r.isLt; omega
    have hmultip := Nat.mul_le_mul_right ((2 * g + 1) - 2) hr
    omega
  have hsum : (∑ r : Fin m, Fintype.card (Index (2 * g + 1)
      ((p - 1) + (m + g) + r.val * ((2 * g + 1) - 2)))) ≤
      m * (((p - 1) + 1 - g) + (m + g) + (m - 1) * ((2 * g + 1) - 2)) := by
    calc
      _ ≤ ∑ _r : Fin m, (((p - 1) + 1 - g) + (m + g) + (m - 1) * ((2 * g + 1) - 2)) :=
        sum_le_sum (fun r _ ↦ hentry r)
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  rw [cardinality_odd g _ hA, cardinality_odd g _ hB]
  have hBcard : (m + g) + 1 - g = m + 1 := by omega
  rw [hBcard]
  apply lt_of_le_of_lt hsum
  have hC : m * (m + g) + m * (m - 1) * ((2 * g + 1) - 2) < ((p - 1) + 1 - g) := by omega
  calc
    _ = m * ((p - 1) + 1 - g) + (m * (m + g) + m * (m - 1) * ((2 * g + 1) - 2)) := by ring
    _ < m * ((p - 1) + 1 - g) + ((p - 1) + 1 - g) := Nat.add_lt_add_left hC _
    _ = _ := by ring

end PaperP1.HyperellipticAuxiliaryDimensionGap
