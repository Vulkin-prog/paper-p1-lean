module

public import PaperP1.Algebra.QuadraticHessianBilinear
public import PaperP1.Algebra.LinearMapPolynomialCoordinates
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-! # An actual homogeneous quadric is carried to a diagonal polynomial by a proved equivalence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticPolynomialDiagonalization

open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [Field F]

def diagonal (w : Fin 4 → F) : MvPolynomial (Fin 4) F :=
  ∑ i, C (w i) * X i ^ 2

theorem evaluation (w v : Fin 4 → F) :
    eval v (diagonal w) = QuadraticMap.weightedSumSquares F w v := by
  simp only [diagonal, map_sum, map_mul, eval_C, eval_X,
    QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two]

theorem homogeneous (w : Fin 4 → F) : (diagonal w).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  exact (isHomogeneous_X_pow i 2).C_mul (w i)

theorem exists_equiv [Infinite F] [Invertible (2 : F)]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2) :
    ∃ (w : Fin 4 → F) (e : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)),
      LinearMapPolynomialCoordinates.substitute e.toLinearMap P = diagonal w := by
  have hex := (QuadraticHessianBilinear.quadratic P).equivalent_weightedSumSquares
  have hdim : Module.finrank F (Fin 4 → F) = 4 := by simp
  rw [hdim] at hex
  obtain ⟨w, ⟨e⟩⟩ := hex
  refine ⟨w, e.symm.toLinearEquiv, ?_⟩
  apply MvPolynomial.funext
  intro v
  rw [LinearMapPolynomialCoordinates.evaluation, evaluation,
    ← QuadraticHessianBilinear.quadratic_evaluation P hP]
  exact e.symm.map_app v

end PaperP1.QuadraticPolynomialDiagonalization
