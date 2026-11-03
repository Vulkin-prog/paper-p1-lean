module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! # The literal three-variable polynomial and its actual partial and total degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TrivariatePolynomialEquiv

open Polynomial

def oneEquiv (R : Type*) [CommSemiring R] : MvPolynomial (Fin 1) R ≃ₐ[R] R[X] :=
  (MvPolynomial.finSuccEquiv R 0).trans (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)))

def twoEquiv (R : Type*) [CommSemiring R] : MvPolynomial (Fin 2) R ≃ₐ[R] R[X][X] :=
  (MvPolynomial.finSuccEquiv R 1).trans (Polynomial.mapAlgEquiv (oneEquiv R))

def threeEquiv (R : Type*) [CommSemiring R] : MvPolynomial (Fin 3) R ≃ₐ[R] R[X][X][X] :=
  (MvPolynomial.finSuccEquiv R 2).trans (Polynomial.mapAlgEquiv (twoEquiv R))

def asMvPolynomial (R : Type*) [CommSemiring R] (P : R[X][X][X]) : MvPolynomial (Fin 3) R :=
  (threeEquiv R).symm P

theorem threeEquiv_X_zero (R : Type*) [CommSemiring R] :
    threeEquiv R (MvPolynomial.X (0 : Fin 3)) = (X : R[X][X][X]) := by
  change ((MvPolynomial.finSuccEquiv R 2 (MvPolynomial.X 0)).map (twoEquiv R).toRingHom) = X
  rw [MvPolynomial.finSuccEquiv_X_zero, map_X]

theorem threeEquiv_X_one (R : Type*) [CommSemiring R] :
    threeEquiv R (MvPolynomial.X (1 : Fin 3)) = C (X : R[X][X]) := by
  change ((MvPolynomial.finSuccEquiv R 2 (MvPolynomial.X (0 : Fin 2).succ)).map (twoEquiv R).toRingHom) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, map_C]
  change C ((MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X 0)).map (oneEquiv R).toRingHom) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, map_X]

theorem threeEquiv_X_two (R : Type*) [CommSemiring R] :
    threeEquiv R (MvPolynomial.X (2 : Fin 3)) = C (C (X : R[X])) := by
  change ((MvPolynomial.finSuccEquiv R 2 (MvPolynomial.X (0 : Fin 1).succ.succ)).map (twoEquiv R).toRingHom) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, map_C]
  change C ((MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (0 : Fin 1).succ)).map (oneEquiv R).toRingHom) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, map_C]
  change C (C ((MvPolynomial.finSuccEquiv R 0 (MvPolynomial.X 0)).map
    (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingHom)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, map_X]

theorem threeEquiv_natDegree (R : Type*) [CommSemiring R] (P : MvPolynomial (Fin 3) R) :
    (threeEquiv R P).natDegree = P.degreeOf 0 := by
  change ((MvPolynomial.finSuccEquiv R 2 P).map (twoEquiv R).toRingHom).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective (twoEquiv R).injective, MvPolynomial.natDegree_finSuccEquiv]

theorem degreeOf_sum_coordinate (R : Type*) [CommSemiring R] (P : R[X][X][X]) :
    (asMvPolynomial R P).degreeOf 0 = P.natDegree := by
  have hh := threeEquiv_natDegree R (asMvPolynomial R P)
  rw [asMvPolynomial, AlgEquiv.apply_symm_apply] at hh
  exact hh.symm

theorem natDegree_le_totalDegree (R : Type*) [CommSemiring R] (P : R[X][X][X]) :
    P.natDegree ≤ (asMvPolynomial R P).totalDegree := by
  rw [← degreeOf_sum_coordinate R P]
  exact MvPolynomial.degreeOf_le_totalDegree _ _

theorem irreducible_iff (R : Type*) [CommSemiring R] (P : R[X][X][X]) :
    Irreducible (asMvPolynomial R P) ↔ Irreducible P :=
  MulEquiv.irreducible_iff (threeEquiv R).symm

end PaperP1.TrivariatePolynomialEquiv
