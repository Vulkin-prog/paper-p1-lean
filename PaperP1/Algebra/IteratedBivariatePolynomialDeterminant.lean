module

public import PaperP1.Algebra.BivariatePolynomialDeterminantDivisibility
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # The actual surface divisor for polynomials in two successive variables -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IteratedBivariatePolynomialDeterminant

open Polynomial

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def toMv : R[X][X] →+* MvPolynomial (Fin 2) R :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 2)))
    (MvPolynomial.X (1 : Fin 2))

theorem evaluation (P : R[X][X]) (x y : R) :
    MvPolynomial.eval ![x, y] (toMv P) = P.evalEval x y := by
  have he : (MvPolynomial.eval ![x, y]).comp (toMv (R := R)) =
      Polynomial.evalEvalRingHom x y := by
    ext <;> simp [toMv, RingHom.comp_apply]
  exact RingHom.congr_fun he P

theorem polynomial_dvd (p : R) (P : ι → R[X][X]) (L : ℕ) (x y : ι → R)
    (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ Matrix.det (fun i j ↦ (P i).evalEval (x j) (y j)) := by
  have hd := BivariatePolynomialDeterminantDivisibility.polynomial_dvd
    p (fun i ↦ toMv (P i)) L x y hx hy
  simpa only [evaluation] using hd

theorem congruent_polynomial_dvd (p : R) (P : ι → R[X][X]) (L : ℕ) (x y : ι → R)
    (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) (A : Matrix ι ι R)
    (hA : ∀ i j, p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A i j - (P i).evalEval (x j) (y j)) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A.det := by
  apply BivariatePolynomialDeterminantDivisibility.congruent_polynomial_dvd
    p (fun i ↦ toMv (P i)) L x y hx hy A
  simpa only [evaluation] using hA

end PaperP1.IteratedBivariatePolynomialDeterminant
