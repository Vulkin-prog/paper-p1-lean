module

public import PaperP1.Algebra.NativeVeroneseAffineIdeal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

/-! # Exact native affine coordinates and every original base monomial -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NativeAffineMonomialCoordinates
open Polynomial Finset
open PaperP1.NativeAffineChart PaperP1.HomogeneousSplitRadicalChart
open PaperP1.TrivariatePolynomialEquiv

theorem specialization_X0 (F : Type*) [Field F] :
    specialization F (MvPolynomial.X (0 : Fin 3)) = (X : F[X][X]) := by
  change chart F (threeEquiv F (MvPolynomial.X (0 : Fin 3))) = _
  rw [threeEquiv_X_zero]
  exact Polynomial.map_X _

theorem specialization_X1 (F : Type*) [Field F] :
    specialization F (MvPolynomial.X (1 : Fin 3)) = C (X : F[X]) := by
  change chart F (threeEquiv F (MvPolynomial.X (1 : Fin 3))) = _
  rw [threeEquiv_X_one]
  change (C (X : F[X][X])).map (Polynomial.mapRingHom (evalRingHom (1 : F))) = _
  rw [Polynomial.map_C]
  exact congrArg C (Polynomial.map_X (evalRingHom (1 : F)))

theorem specialization_monomial (F : Type*) [Field F] (e : Fin 3 →₀ ℕ) :
    specialization F (MvPolynomial.monomial e 1) = (C (X : F[X]))^(e 1) * X^(e 0) := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, map_mul, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), map_prod, Fin.prod_univ_three]
  rw [map_pow, map_pow, map_pow, specialization_X0, specialization_X1,
    PaperP1.NativeVeroneseAffineIdeal.specialization_Z, one_pow, mul_one, mul_comm]

theorem specialization_X (F : Type*) [Field F] (j : Fin 3) :
    specialization F (MvPolynomial.X j) = ![(X : F[X][X]), C (X : F[X]), 1] j := by
  fin_cases j
  · exact specialization_X0 F
  · exact specialization_X1 F
  · exact PaperP1.NativeVeroneseAffineIdeal.specialization_Z F

end PaperP1.NativeAffineMonomialCoordinates
