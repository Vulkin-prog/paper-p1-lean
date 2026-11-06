module

public import PaperP1.Algebra.PolynomialTangentWronskian
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Actual coefficient and Sylvester determinant degree bounds for multivariate resultants -/

set_option autoImplicit false

@[expose] public noncomputable section
namespace PaperP1.PolynomialCoefficientResultantDegree
open Polynomial Finset
open scoped Classical

section Degree
variable {σ F : Type*} [CommRing F]

theorem derivative_coefficient_degree (P : (MvPolynomial σ F)[X]) (D : ℕ)
    (hP : ∀ i, (P.coeff i).totalDegree ≤ D) (i : ℕ) :
    (P.derivative.coeff i).totalDegree ≤ D := by
  have hc : (i : MvPolynomial σ F) + 1 = MvPolynomial.C ((i : F) + 1) := by
    simp only [map_add, map_natCast, map_one]
  rw [coeff_derivative, hc]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [MvPolynomial.totalDegree_C, add_zero]
    exact hP (i+1))

theorem sylvester_entry_degree (P Q : (MvPolynomial σ F)[X]) (m n D : ℕ)
    (hP : ∀ i, (P.coeff i).totalDegree ≤ D) (hQ : ∀ i, (Q.coeff i).totalDegree ≤ D)
    (i j : Fin (m+n)) : (sylvester P Q m n i j).totalDegree ≤ D := by
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hQ _
    · simp
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hP _
    · simp

theorem resultant_degree (P Q : (MvPolynomial σ F)[X]) (D : ℕ)
    (hP : ∀ i, (P.coeff i).totalDegree ≤ D) (hQ : ∀ i, (Q.coeff i).totalDegree ≤ D) :
    (P.resultant Q).totalDegree ≤ (P.natDegree + Q.natDegree) * D := by
  have hd := PaperP1.PolynomialTangentWronskian.determinant_row_degree
    (sylvester P Q P.natDegree Q.natDegree) (fun _ ↦ D)
    (sylvester_entry_degree P Q _ _ D hP hQ)
  change (P.resultant Q).totalDegree ≤ _ at hd
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using hd

theorem derivative_resultant_degree (P : (MvPolynomial σ F)[X]) (D : ℕ)
    (hP : ∀ i, (P.coeff i).totalDegree ≤ D) :
    (P.resultant P.derivative).totalDegree ≤ 2 * P.natDegree * D := by
  apply (resultant_degree P P.derivative D hP (derivative_coefficient_degree P D hP)).trans
  exact Nat.mul_le_mul_right D (by have := natDegree_derivative_le P; omega)
end Degree
end PaperP1.PolynomialCoefficientResultantDegree
