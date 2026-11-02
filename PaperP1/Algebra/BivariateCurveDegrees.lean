module

public import PaperP1.Algebra.BivariateTotalDegree
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Partial degrees, differentiation and total degree for the actual curve polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateCurveDegrees

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree

theorem degreeX_le_of_coefficients (P : ℤ[X][X]) (d : ℕ)
    (h : ∀ i, (P.coeff i).natDegree ≤ d) : degreeX P ≤ d := by
  unfold degreeX
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext i
  rw [coeff_swap, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt ((h i).trans_lt hn)

theorem degreeX_derivative_le (P : ℤ[X][X]) : degreeX P.derivative ≤ degreeX P := by
  apply degreeX_le_of_coefficients
  intro n
  have hc : P.derivative.coeff n = P.coeff (n + 1) * (((n + 1 : ℕ) : ℤ[X])) := by
    simpa only [Nat.cast_add, Nat.cast_one] using coeff_derivative P n
  rw [hc]
  calc
    _ ≤ (P.coeff (n + 1)).natDegree + (((n + 1 : ℕ) : ℤ[X])).natDegree := natDegree_mul_le
    _ = (P.coeff (n + 1)).natDegree := by rw [natDegree_natCast, add_zero]
    _ ≤ _ := natDegree_coeff_le_degreeX P _

theorem degreeX_le_total (P : ℤ[X][X]) : degreeX P ≤ totalDegree P := by
  apply degreeX_le_of_coefficients
  intro i
  by_cases hi : P.coeff i = 0
  · rw [hi, natDegree_zero]
    exact Nat.zero_le _
  · have hc : (P.coeff i).coeff (P.coeff i).natDegree ≠ 0 := by
      simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hi
    have h := coefficient_degree_le P (P.coeff i).natDegree i hc
    omega

theorem degreeY_le_total (P : ℤ[X][X]) : degreeY P ≤ totalDegree P := by
  by_cases hP : P = 0
  · subst P
    simp only [degreeY, natDegree_zero, totalDegree_zero, le_refl]
  · have hr : P.coeff P.natDegree ≠ 0 := by
      simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hP
    have hc : (P.coeff P.natDegree).coeff (P.coeff P.natDegree).natDegree ≠ 0 := by
      simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hr
    have h := coefficient_degree_le P (P.coeff P.natDegree).natDegree P.natDegree hc
    change P.natDegree ≤ totalDegree P
    omega

theorem degreeX_swap (P : ℤ[X][X]) : degreeX (Bivariate.swap P) = degreeY P := by
  unfold degreeX degreeY
  rw [Bivariate.swap_swap_apply]

theorem degreeY_swap (P : ℤ[X][X]) : degreeY (Bivariate.swap P) = degreeX P := rfl

end PaperP1.BivariateCurveDegrees
