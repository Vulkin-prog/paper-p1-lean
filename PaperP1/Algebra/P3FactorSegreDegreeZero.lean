module

public import PaperP1.Algebra.P3FactorSegreGrading
public import PaperP1.Algebra.GradedSurjectiveChartMap
public import PaperP1.Algebra.HomogeneousPolynomialEvaluation

/-! # The literal degree-zero ring of the Segre coefficient quotient is finite over the integers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorSegreDegreeZero

open MvPolynomial P3FactorSegreRelations P3FactorSegreGrading

attribute [local instance] MvPolynomial.gradedAlgebra P3FactorSegreGrading.grading

theorem zero_element_scalar (e f : ℕ) (x : piece e f 0) :
    ∃ n : ℤ, x.val = algebraMap ℤ (Quotient e f) n := by
  obtain ⟨P, hP, hPx⟩ := Submodule.mem_map.mp x.property
  have hC : P = C (P.coeff 0) := HomogeneousPolynomialEvaluation.homogeneous_zero_eq_C P hP
  refine ⟨P.coeff 0, ?_⟩
  rw [← hPx]
  conv_lhs => rw [hC]
  simp

theorem zero_algebra_surjective (e f : ℕ) : Function.Surjective (algebraMap ℤ (piece e f 0)) := by
  intro x
  obtain ⟨n, hn⟩ := zero_element_scalar e f x
  refine ⟨n, Subtype.ext ?_⟩
  change algebraMap ℤ (Quotient e f) n = x.val
  exact hn.symm

theorem zero_module_finite (e f : ℕ) : Module.Finite ℤ (piece e f 0) :=
  Module.Finite.of_surjective (Algebra.linearMap ℤ (piece e f 0)) (zero_algebra_surjective e f)

theorem over_zero_finite_type (e f : ℕ) : Algebra.FiniteType (piece e f 0) (Quotient e f) := by
  let : Algebra.FiniteType ℤ (Quotient e f) := finite_type e f
  let : IsScalarTower ℤ (piece e f 0) (Quotient e f) := by
    constructor
    intro n r x
    change (n • r.val) * x = n • (r.val * x)
    exact smul_mul_assoc n r.val x
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℤ (piece e f 0) (Quotient e f)

end PaperP1.P3FactorSegreDegreeZero
