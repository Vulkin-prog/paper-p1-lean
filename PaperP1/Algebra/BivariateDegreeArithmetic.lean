module

public import PaperP1.Algebra.BivariateDegrees

/-! # Elementary partial-degree bounds for bivariate sums and products -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.BivariateDegreeArithmetic

open Polynomial PaperP1.BivariateDegrees

theorem mul_bound (P Q : ℤ[X][X]) (m n : ℕ)
    (hP : degreeX P ≤ m ∧ degreeY P ≤ m) (hQ : degreeX Q ≤ n ∧ degreeY Q ≤ n) :
    degreeX (P * Q) ≤ m + n ∧ degreeY (P * Q) ≤ m + n := by
  constructor
  · change (Bivariate.swap (P * Q)).natDegree ≤ m + n
    rw [map_mul]
    exact natDegree_mul_le.trans (Nat.add_le_add hP.1 hQ.1)
  · exact natDegree_mul_le.trans (Nat.add_le_add hP.2 hQ.2)

theorem add_bound (P Q : ℤ[X][X]) (m : ℕ)
    (hP : degreeX P ≤ m ∧ degreeY P ≤ m) (hQ : degreeX Q ≤ m ∧ degreeY Q ≤ m) :
    degreeX (P + Q) ≤ m ∧ degreeY (P + Q) ≤ m := by
  constructor
  · change (Bivariate.swap (P + Q)).natDegree ≤ m
    rw [map_add]
    exact natDegree_add_le_of_degree_le hP.1 hQ.1
  · exact natDegree_add_le_of_degree_le hP.2 hQ.2

theorem sub_bound (P Q : ℤ[X][X]) (m : ℕ)
    (hP : degreeX P ≤ m ∧ degreeY P ≤ m) (hQ : degreeX Q ≤ m ∧ degreeY Q ≤ m) :
    degreeX (P - Q) ≤ m ∧ degreeY (P - Q) ≤ m := by
  constructor
  · change (Bivariate.swap (P - Q)).natDegree ≤ m
    rw [map_sub]
    exact (natDegree_sub_le _ _).trans (max_le hP.1 hQ.1)
  · exact (natDegree_sub_le _ _).trans (max_le hP.2 hQ.2)

theorem pow_bound (P : ℤ[X][X]) (m n : ℕ) (hP : degreeX P ≤ m ∧ degreeY P ≤ m) :
    degreeX (P ^ n) ≤ n * m ∧ degreeY (P ^ n) ≤ n * m := by
  constructor
  · change (Bivariate.swap (P ^ n)).natDegree ≤ n * m
    rw [map_pow]
    exact natDegree_pow_le_of_le n hP.1
  · exact natDegree_pow_le_of_le n hP.2

end PaperP1.BivariateDegreeArithmetic
