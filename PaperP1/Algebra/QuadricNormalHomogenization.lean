module

public import PaperP1.Diophantine.FiniteFieldQuadricNormalCount
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.GroupWithZero.Associated

/-! # A geometrically meaningful quadratic normal form has a nonzero tangent section -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadricNormalHomogenization

open MvPolynomial
open scoped Classical

variable {F : Type*} [Field F]

def polynomial (L Q : MvPolynomial (Fin 3) F) : MvPolynomial (Fin 4) F :=
  rename Fin.succ Q + X 0 * rename Fin.succ L

theorem homogeneous (L Q : MvPolynomial (Fin 3) F)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2) :
    (polynomial L Q).IsHomogeneous 2 :=
  hQ.rename_isHomogeneous.add ((isHomogeneous_X F 0).mul hL.rename_isHomogeneous)

theorem evaluation (L Q : MvPolynomial (Fin 3) F) (v : Fin 3 → F) :
    eval (Fin.cons 1 v) (polynomial L Q) = eval v L + eval v Q := by
  simp only [polynomial, map_add, map_mul, eval_X, Fin.cons_zero, one_mul, eval_rename]
  change eval v Q + eval v L = eval v L + eval v Q
  exact add_comm _ _

theorem boundary_eq_coefficient (Q : MvPolynomial (Fin 3) F) :
    FiniteFieldQuadricNormalCount.boundary Q = (finSuccEquiv F 2 Q).coeff 0 := by
  have he : FiniteFieldQuadricNormalCount.boundary (F := F) =
      (Polynomial.evalRingHom 0).comp (finSuccEquiv F 2).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [FiniteFieldQuadricNormalCount.boundary, finSuccEquiv_apply]
    · intro i
      cases i using Fin.cases <;> simp [FiniteFieldQuadricNormalCount.boundary, finSuccEquiv_apply]
  have hh := RingHom.congr_fun he Q
  change FiniteFieldQuadricNormalCount.boundary Q = (finSuccEquiv F 2 Q).eval 0 at hh
  exact hh.trans (Polynomial.coeff_zero_eq_eval_zero _).symm

theorem variable_dvd_of_boundary_zero (Q : MvPolynomial (Fin 3) F)
    (hQ : FiniteFieldQuadricNormalCount.boundary Q = 0) : X (0 : Fin 3) ∣ Q := by
  have hd : Polynomial.X ∣ finSuccEquiv F 2 Q := by
    apply Polynomial.X_dvd_iff.mpr
    rw [← boundary_eq_coefficient, hQ]
  have hx : (finSuccEquiv F 2).symm Polynomial.X = X 0 := by
    apply (finSuccEquiv F 2).injective
    rw [AlgEquiv.apply_symm_apply, finSuccEquiv_X_zero]
  have hh := map_dvd (finSuccEquiv F 2).symm.toRingHom hd
  change (finSuccEquiv F 2).symm Polynomial.X ∣ (finSuccEquiv F 2).symm (finSuccEquiv F 2 Q) at hh
  rw [hx, AlgEquiv.symm_apply_apply] at hh
  exact hh

theorem boundary_nonzero (a : F) (Q : MvPolynomial (Fin 3) F) (hQ : Q.IsHomogeneous 2)
    (hirr : Irreducible (polynomial (C a * X 0) Q)) :
    FiniteFieldQuadricNormalCount.boundary Q ≠ 0 := by
  intro hz
  have hdQ : X (1 : Fin 4) ∣ rename Fin.succ Q := by
    have hh := map_dvd (rename Fin.succ) (variable_dvd_of_boundary_zero Q hz)
    rw [rename_X, show (0 : Fin 3).succ = (1 : Fin 4) by decide] at hh
    exact hh
  have hdL : X (1 : Fin 4) ∣ X 0 * rename Fin.succ (C a * X 0) := by
    simp only [map_mul, rename_C, rename_X]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
  have hd : X (1 : Fin 4) ∣ polynomial (C a * X 0) Q := dvd_add hdQ hdL
  have hassoc := (hirr.dvd_iff.mp hd).resolve_left (prime_X (i := (1 : Fin 4))).not_isUnit
  have hback : polynomial (C a * X 0) Q ∣ X (1 : Fin 4) := hassoc.dvd
  have hdeg := totalDegree_le_of_dvd_of_isDomain hback (X_ne_zero (1 : Fin 4))
  have hhom := homogeneous (C a * X 0) Q (isHomogeneous_C_mul_X a 0) hQ
  rw [hhom.totalDegree hirr.ne_zero, totalDegree_X] at hdeg
  exact (by decide : ¬2 ≤ 1) hdeg

end PaperP1.QuadricNormalHomogenization
