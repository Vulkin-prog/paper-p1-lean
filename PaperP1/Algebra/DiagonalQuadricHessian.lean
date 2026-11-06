module

public import PaperP1.Algebra.QuadraticPolynomialDiagonalization
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Exact Hessian and rank of an actual diagonal quadratic polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DiagonalQuadricHessian

open MvPolynomial HomogeneousQuadraticHessian QuadraticPolynomialDiagonalization
open scoped Classical

variable {F : Type*} [Field F]

theorem derivative (w : Fin 4 → F) (i : Fin 4) :
    pderiv i (diagonal w) = C (w i) * (X i + X i) := by
  have hterm (k : Fin 4) : pderiv i (C (w k) * X k ^ 2) =
      if k = i then C (w i) * (X i + X i) else 0 := by
    by_cases hk : k = i
    · subst k
      simp [pow_two]
    · simp [pow_two, hk]
  simp only [diagonal, map_sum, hterm]
  simp

theorem entry_diagonal (w : Fin 4 → F) (i j : Fin 4) :
    entry (diagonal w) i j = if i = j then 2 * w i else 0 := by
  rw [entry, derivative]
  by_cases hij : i = j
  · subst j
    simp [two_mul]
    ring
  · simp [hij]

theorem matrix_diagonal (w : Fin 4 → F) :
    Matrix.of (entry (diagonal w)) = Matrix.diagonal (fun i ↦ 2 * w i) := by
  ext i j
  simp only [Matrix.of_apply, entry_diagonal, Matrix.diagonal_apply]

theorem rank [Invertible (2 : F)] (w : Fin 4 → F) :
    (Matrix.of (entry (diagonal w))).rank =
      ((Finset.univ : Finset (Fin 4)).filter (fun i ↦ w i ≠ 0)).card := by
  rw [matrix_diagonal, Matrix.rank_diagonal]
  have htwo : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  calc
    _ = Fintype.card {i : Fin 4 // w i ≠ 0} := Fintype.card_congr
      (Equiv.subtypeEquivRight (fun i ↦ (mul_ne_zero_iff.trans (and_iff_right htwo))))
    _ = _ := Fintype.card_subtype _

end PaperP1.DiagonalQuadricHessian
