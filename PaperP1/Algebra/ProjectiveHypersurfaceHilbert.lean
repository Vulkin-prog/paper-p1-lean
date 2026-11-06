module

public import PaperP1.Algebra.QuaternaryPolynomialHilbert
public import PaperP1.Algebra.RegularSurfaceHilbertSection
public import PaperP1.Algebra.HomogeneousQuotientGrading

/-! # The actual homogeneous coordinate quotient of a surface hypersurface has its genuine quadratic Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveHypersurfaceHilbert

open Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

def polynomial (d : ℕ) : ℚ[X] := C ((d : ℚ) / 2) * X ^ 2 + C ((4 * (d : ℚ) - (d : ℚ) ^ 2) / 2) * X +
  C (((d : ℚ) ^ 3 - 6 * (d : ℚ) ^ 2 + 11 * (d : ℚ)) / 6)

theorem difference (d : ℕ) : QuadraticHilbertDifference.difference QuaternaryPolynomialHilbert.polynomial d = polynomial d := by
  apply Polynomial.funext
  intro t
  simp only [QuadraticHilbertDifference.difference, QuaternaryPolynomialHilbert.polynomial, polynomial,
    eval_sub, eval_comp, eval_X, eval_C, eval_add, eval_mul, eval_pow, eval_one]
  ring

theorem isHilbertPolynomial (F : Type*) [Field F] (d : ℕ) (q : MvPolynomial (Fin 4) F)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) :
    GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule (Fin 4) F) (Ideal.span {q}))
      (polynomial d) := by
  let (n : ℕ) : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 4) F n) :=
    MvPolynomialHilbert.piece_finite F (Fin 4) n
  have hh := RegularSurfaceHilbertSection.polynomial_difference (MvPolynomial.homogeneousSubmodule (Fin 4) F)
    QuaternaryPolynomialHilbert.polynomial (QuaternaryPolynomialHilbert.isHilbertPolynomial F) hq
    (fun a b he ↦ mul_right_cancel₀ hq0 he)
  rw [difference] at hh
  exact hh

theorem natDegree_le (d : ℕ) : (polynomial d).natDegree ≤ 2 := by unfold polynomial; compute_degree

theorem coeff_two (d : ℕ) : (polynomial d).coeff 2 = (d : ℚ) / 2 := by simp [polynomial]

end PaperP1.ProjectiveHypersurfaceHilbert
