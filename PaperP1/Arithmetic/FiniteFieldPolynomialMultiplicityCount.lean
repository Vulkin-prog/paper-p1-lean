module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Literal root multiplicities bound a finite set by the actual polynomial degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldPolynomialMultiplicityCount

open Finset Polynomial
open scoped Classical

theorem cardinality {F : Type*} [Field F] [Fintype F] (P : F[X]) (S : Finset F) (m : ℕ)
    (hS : ∀ x ∈ S, m ≤ rootMultiplicity x P) : m * S.card ≤ P.natDegree := by
  calc
    _ = ∑ _x ∈ S, m := by simp only [sum_const, nsmul_eq_mul, Nat.mul_comm, Nat.cast_id]
    _ ≤ ∑ x ∈ S, rootMultiplicity x P := sum_le_sum hS
    _ ≤ ∑ x : F, rootMultiplicity x P := sum_le_sum_of_subset (subset_univ S)
    _ = P.roots.card := by
      simpa only [Polynomial.count_roots] using
        (Multiset.sum_count_eq_card (s := (univ : Finset F)) (m := P.roots) (fun x _ ↦ mem_univ x))
    _ ≤ P.natDegree := Polynomial.card_roots' P

end PaperP1.FiniteFieldPolynomialMultiplicityCount
