module

public import PaperP1.Algebra.PolynomialTangentDegree

/-! # Exact plane-coordinate transposition

Polynomial degree, evaluation and formal partial derivatives commute with the
actual coordinate equivalence; no geometric identification is left implicit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneCoordinateSwap

open MvPolynomial

variable {R : Type*} [CommRing R]

def index : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

def polynomial (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R := rename index P

def point (z : Fin 2 → R) : Fin 2 → R := fun i ↦ z (index i)

@[simp] theorem index_zero : index 0 = 1 := by decide

@[simp] theorem index_one : index 1 = 0 := by decide

@[simp] theorem index_twice (i : Fin 2) : index (index i) = i := by
  exact Equiv.swap_apply_self 0 1 i

omit [CommRing R] in
@[simp] theorem point_twice (z : Fin 2 → R) : point (point z) = z := by
  funext i
  simp only [point, index_twice]

@[simp] theorem polynomial_twice (P : MvPolynomial (Fin 2) R) : polynomial (polynomial P) = P := by
  change rename index (rename index P) = P
  rw [rename_rename]
  have hh : (index : Fin 2 → Fin 2) ∘ index = id := by
    funext i
    exact index_twice i
  rw [hh, rename_id_apply]

theorem evaluation (P : MvPolynomial (Fin 2) R) (z : Fin 2 → R) :
    eval z (polynomial P) = eval (point z) P := by
  exact eval_rename index z P

@[simp] theorem degree (P : MvPolynomial (Fin 2) R) :
    (polynomial P).totalDegree = P.totalDegree :=
  totalDegree_renameEquiv index P

theorem pderiv_swap (P : MvPolynomial (Fin 2) R) (i : Fin 2) :
    pderiv (index i) (polynomial P) = polynomial (pderiv i P) :=
  pderiv_rename index.injective i P

theorem evaluation_partial (P : MvPolynomial (Fin 2) R) (z : Fin 2 → R) (i : Fin 2) :
    eval (point z) (pderiv (index i) (polynomial P)) = eval z (pderiv i P) := by
  rw [pderiv_swap, evaluation, point_twice]

theorem evaluation_pderiv (P : MvPolynomial (Fin 2) R) (z : Fin 2 → R) (i : Fin 2) :
    eval z (pderiv (index i) (polynomial P)) = eval (point z) (pderiv i P) := by
  rw [pderiv_swap, evaluation]

theorem evaluation_polynomial_at_point (P : MvPolynomial (Fin 2) R) (z : Fin 2 → R) :
    eval (point z) (polynomial P) = eval z P := by
  rw [evaluation, point_twice]

end PaperP1.PlaneCoordinateSwap
