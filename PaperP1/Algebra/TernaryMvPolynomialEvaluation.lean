module

public import PaperP1.Algebra.TernaryPolynomialEvaluation
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! # Actual three-coordinate polynomials as successive univariate polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryMvPolynomialEvaluation

variable {R : Type*} [CommRing R]

def iterated : MvPolynomial (Fin 3) R →+* Polynomial (Polynomial (Polynomial R)) :=
  MvPolynomial.eval₂Hom (R := R) (S₁ := Polynomial (Polynomial (Polynomial R)))
    (Polynomial.C.comp (Polynomial.C.comp (Polynomial.C : R →+* Polynomial R)))
    ![Polynomial.C (Polynomial.C Polynomial.X), Polynomial.C Polynomial.X, Polynomial.X]

theorem evaluation (P : MvPolynomial (Fin 3) R) (a b c : R) :
    TernaryPolynomialEvaluation.evaluation a b c (iterated P) = MvPolynomial.eval ![a, b, c] P := by
  have he : (TernaryPolynomialEvaluation.evaluation a b c).comp (iterated (R := R)) =
      MvPolynomial.eval ![a, b, c] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [iterated, TernaryPolynomialEvaluation.evaluation]
    · intro i
      fin_cases i <;> simp [iterated, TernaryPolynomialEvaluation.evaluation]
  exact RingHom.congr_fun he P

theorem derivative (P : MvPolynomial (Fin 3) R) :
    (iterated P).derivative = iterated (MvPolynomial.pderiv 2 P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp [iterated]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, Polynomial.derivative_mul, hP]
    fin_cases i <;> simp [iterated, add_comm] <;> ring

end PaperP1.TernaryMvPolynomialEvaluation
