module

public import PaperP1.Algebra.HomogeneousQuadraticHessian
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # The exact bilinear and quadratic forms of the actual polynomial Hessian -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticHessianBilinear

open MvPolynomial Finset HomogeneousQuadraticHessian
open scoped Classical

variable {F σ : Type*} [Field F] [Fintype σ] [DecidableEq σ]

def bilinear (P : MvPolynomial σ F) : LinearMap.BilinForm F (σ → F) :=
  Matrix.toBilin' (Matrix.of (entry P))

theorem symmetric (P : MvPolynomial σ F) : (bilinear P).IsSymm := by
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  ext i j
  exact HomogeneousQuadraticHessian.symmetric P j i

theorem diagonal_evaluation (P : MvPolynomial σ F) (hP : P.IsHomogeneous 2) (v : σ → F) :
    bilinear P v v = 2 * eval v P := by
  rw [bilinear, Matrix.toBilin'_apply]
  simp only [Matrix.of_apply]
  calc
    _ = ∑ i, ∑ j, entry P i j * v i * v j := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := evaluation_identity P hP v

def quadratic [Invertible (2 : F)] (P : MvPolynomial σ F) : QuadraticForm F (σ → F) :=
  ⅟(2 : F) • (bilinear P).toQuadraticMap

theorem quadratic_evaluation [Invertible (2 : F)]
    (P : MvPolynomial σ F) (hP : P.IsHomogeneous 2) (v : σ → F) :
    quadratic P v = eval v P := by
  change ⅟(2 : F) * bilinear P v v = eval v P
  rw [diagonal_evaluation P hP v, ← mul_assoc, invOf_mul_self, one_mul]

end PaperP1.QuadraticHessianBilinear
