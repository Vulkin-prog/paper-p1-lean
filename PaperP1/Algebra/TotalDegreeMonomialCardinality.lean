module

public import PaperP1.Algebra.TotalDegreeMonomialFamily
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact cardinality of the actual plane total-degree monomial index type -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TotalDegreeMonomialCardinality

open Finset TotalDegreeMonomials


def fiberEquiv (k : ℕ) : Index k ≃ (Σ a : Fin (k + 1), Fin (k + 1 - a.val)) where
  toFun i := ⟨i.val.1, ⟨i.val.2.val, by have := i.property; omega⟩⟩
  invFun i := ⟨(i.1, ⟨i.2.val, by have := i.2.isLt; omega⟩), by
    change i.1.val + i.2.val ≤ k
    have := i.2.isLt
    omega⟩
  left_inv i := rfl
  right_inv i := by cases i; rfl

theorem card_twice (k : ℕ) : 2 * Fintype.card (Index k) = (k + 1) * (k + 2) := by
  have hc : Fintype.card (Index k) = ∑ a : Fin (k + 1), (k + 1 - a.val) := by
    rw [Fintype.card_congr (fiberEquiv k), Fintype.card_sigma]
    simp only [Fintype.card_fin]
  have hsum : (∑ a : Fin (k + 1), (k + 1 - a.val)) + (∑ a : Fin (k + 1), a.val) =
      (k + 1) * (k + 1) := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _a : Fin (k + 1), (k + 1) := sum_congr rfl (fun a _ha ↦ Nat.sub_add_cancel (by have := a.isLt; omega))
      _ = _ := by simp
  have hlow : (∑ a : Fin (k + 1), a.val) * 2 = (k + 1) * k := by
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ ↦ a) (k + 1)]
    simpa only [Nat.add_sub_cancel] using sum_range_id_mul_two (k + 1)
  rw [hc]
  nlinarith only [hsum, hlow]

theorem card_formula (k : ℕ) : Fintype.card (Index k) = (k + 1) * (k + 2) / 2 := by
  have hh := card_twice k
  omega

end PaperP1.TotalDegreeMonomialCardinality
