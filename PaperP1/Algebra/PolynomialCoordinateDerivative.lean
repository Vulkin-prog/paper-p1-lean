module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Actual distinguished-coordinate partial differentiation agrees with the polynomial chart derivative -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialCoordinateDerivative

open MvPolynomial

theorem finSucc_pderiv_zero {F : Type*} [CommRing F] {n : ℕ}
    (q : MvPolynomial (Fin (n + 1)) F) :
    finSuccEquiv F n (pderiv 0 q) = Polynomial.derivative (finSuccEquiv F n q) := by
  classical
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro d
  have hcons : d.cons i + Finsupp.single 0 1 = d.cons (i + 1) := by
    ext j
    cases j using Fin.cases <;> simp
  rw [finSuccEquiv_coeff_coeff, coeff_pderiv, Polynomial.coeff_derivative]
  have hcast : (i : MvPolynomial (Fin n) F) + 1 = C ((i : F) + 1) := by simp
  rw [hcast, mul_comm _ (C _), coeff_C_mul, finSuccEquiv_coeff_coeff]
  rw [hcons, Finsupp.cons_zero]
  ring

end PaperP1.PolynomialCoordinateDerivative
