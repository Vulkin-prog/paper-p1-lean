module

public import PaperP1.Algebra.QuadraticHessianBilinear
public import PaperP1.Algebra.LinearMapPolynomialCoordinates
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Determinant

/-! # Actual Hessian congruence and rank transport under constructed linear coordinate changes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticHessianLinearTransport

open MvPolynomial HomogeneousQuadraticHessian QuadraticHessianBilinear
open scoped Classical

variable {F σ : Type*} [Field F] [Fintype σ] [DecidableEq σ] [Invertible (2 : F)]

theorem bilinear_transport (P : MvPolynomial σ F) (hP : P.IsHomogeneous 2)
    (f : (σ → F) →ₗ[F] (σ → F)) :
    bilinear (LinearMapPolynomialCoordinates.substitute f P) = (bilinear P).comp f f := by
  let : NeZero (2 : F) := ⟨(isUnit_of_invertible (2 : F)).ne_zero⟩
  have hs : ((bilinear P).comp f f).IsSymm :=
    ⟨fun x y ↦ (QuadraticHessianBilinear.symmetric P).eq (f x) (f y)⟩
  apply LinearMap.BilinForm.ext_of_isSymm (QuadraticHessianBilinear.symmetric _) hs
  intro v
  rw [diagonal_evaluation _ (LinearMapPolynomialCoordinates.homogeneous f P hP),
    LinearMapPolynomialCoordinates.evaluation]
  exact (diagonal_evaluation P hP (f v)).symm

theorem matrix_transport (P : MvPolynomial σ F) (hP : P.IsHomogeneous 2)
    (f : (σ → F) →ₗ[F] (σ → F)) :
    Matrix.of (entry (LinearMapPolynomialCoordinates.substitute f P)) =
      f.toMatrix'.transpose * Matrix.of (entry P) * f.toMatrix' := by
  have he := congrArg LinearMap.BilinForm.toMatrix' (bilinear_transport P hP f)
  simpa only [bilinear, LinearMap.BilinForm.toMatrix'_comp,
    LinearMap.BilinForm.toMatrix'_toBilin'] using he

theorem rank_transport (P : MvPolynomial σ F) (hP : P.IsHomogeneous 2)
    (e : (σ → F) ≃ₗ[F] (σ → F)) :
    (Matrix.of (entry (LinearMapPolynomialCoordinates.substitute e.toLinearMap P))).rank =
      (Matrix.of (entry P)).rank := by
  rw [matrix_transport P hP]
  let E : Matrix σ σ F := e.toLinearMap.toMatrix'
  have hdet : IsUnit E.det := by
    simpa only [LinearMap.toMatrix_eq_toMatrix'] using
      e.isUnit_det (Pi.basisFun F σ) (Pi.basisFun F σ)
  have hdetT : IsUnit E.transpose.det := by
    rw [Matrix.det_transpose]
    exact hdet
  change (E.transpose * Matrix.of (entry P) * E).rank = _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det E _ hdet,
    Matrix.rank_mul_eq_right_of_isUnit_det E.transpose _ hdetT]

end PaperP1.QuadraticHessianLinearTransport
