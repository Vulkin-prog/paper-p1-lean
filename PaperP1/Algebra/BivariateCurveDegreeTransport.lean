module

public import PaperP1.Algebra.BivariateIrreducibleHomogenization
public import PaperP1.Algebra.BivariateResultantDegree
public import PaperP1.Algebra.PolynomialScalarProjection
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Generic total-degree bounds for swapping and differentiating a plane equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateCurveDegreeTransport

open Polynomial PaperP1.BivariateIrreducibleHomogenization

variable {R : Type*} [CommRing R]

theorem degree_le_partial_sum (P : R[X][X]) :
    PlaneCurvePointCount.degree P ≤ (Bivariate.swap P).natDegree + P.natDegree := by
  apply Finset.sup_le
  intro i hi
  have hout := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hi)
  have hin := coefficient_degree_le P i
  omega

theorem degree_swap (P : R[X][X]) :
    PlaneCurvePointCount.degree (Bivariate.swap P) = PlaneCurvePointCount.degree P := by
  have hle (Q : R[X][X]) :
      PlaneCurvePointCount.degree (Bivariate.swap Q) ≤ PlaneCurvePointCount.degree Q := by
    apply Finset.sup_le
    intro i hi
    have hrow : (Bivariate.swap Q).coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
    have hc : ((Bivariate.swap Q).coeff i).coeff ((Bivariate.swap Q).coeff i).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hrow
    rw [swap_coefficient] at hc
    have hQrow : Q.coeff ((Bivariate.swap Q).coeff i).natDegree ≠ 0 := by
      intro hz
      exact hc (by rw [hz, coeff_zero])
    have hx := Polynomial.le_natDegree_of_ne_zero hc
    have hd := BivariateResultantDegree.coefficient_row_degree Q _ hQrow
    omega
  exact (hle P).antisymm (by simpa only [Bivariate.swap_swap_apply] using hle (Bivariate.swap P))

theorem degree_derivative (P : R[X][X]) :
    PlaneCurvePointCount.degree P.derivative ≤ PlaneCurvePointCount.degree P - 1 := by
  apply Finset.sup_le
  intro i hi
  have hrow : P.derivative.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have horig : P.coeff (i + 1) ≠ 0 := by
    intro hz
    apply hrow
    rw [Polynomial.coeff_derivative, hz, zero_mul]
  have hd := BivariateResultantDegree.coefficient_row_degree P (i + 1) horig
  have hnat : (P.derivative.coeff i).natDegree ≤ (P.coeff (i + 1)).natDegree := by
    rw [Polynomial.coeff_derivative]
    exact Polynomial.natDegree_mul_le.trans (by simp)
  omega

theorem swap_evaluation (P : R[X][X]) (x y : R) :
    (Bivariate.swap P).evalEval x y = P.evalEval y x := by
  simpa only [Polynomial.coe_aevalAeval_eq_evalEval] using
    (Polynomial.Bivariate.aevalAeval_swap (R := R) x y P)

theorem extend_swap {K L : Type*} [Field K] [Field L] [Algebra K L] (P : K[X][X]) :
    PaperP1.PolynomialScalarProjection.extend (L := L) (Bivariate.swap P) =
      Bivariate.swap (PaperP1.PolynomialScalarProjection.extend P : L[X][X]) := by
  ext i j
  rw [PaperP1.PolynomialScalarProjection.extend_coefficient, swap_coefficient,
    swap_coefficient, PaperP1.PolynomialScalarProjection.extend_coefficient]

end PaperP1.BivariateCurveDegreeTransport
