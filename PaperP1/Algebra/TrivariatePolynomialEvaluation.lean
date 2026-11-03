module

public import PaperP1.Algebra.TrivariatePolynomialEquiv
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Tactic.FinCases

/-! # The three-variable presentation evaluates at the literal source coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TrivariatePolynomialEvaluation

open Polynomial PaperP1.TrivariatePolynomialEquiv

def evaluation (R : Type*) [CommSemiring R] (x y z : R) : R[X][X][X] →+* R :=
  (evalRingHom z).comp (mapRingHom (evalEvalRingHom x y))

theorem evaluation_apply (R : Type*) [CommSemiring R] (x y z : R) (P : R[X][X][X]) :
    evaluation R x y z P = (P.map (evalEvalRingHom x y)).eval z := rfl

theorem evaluation_comp_threeEquiv (R : Type*) [CommSemiring R] (x y z : R) :
    (evaluation R x y z).comp (threeEquiv R).toRingHom = MvPolynomial.eval ![z, y, x] := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change evaluation R x y z (threeEquiv R (algebraMap R (MvPolynomial (Fin 3) R) r)) = _
    rw [(threeEquiv R).commutes]
    simp [evaluation]
  · intro i
    change evaluation R x y z (threeEquiv R (MvPolynomial.X i)) =
      MvPolynomial.eval ![z, y, x] (MvPolynomial.X i)
    fin_cases i
    · simpa [evaluation] using congrArg (evaluation R x y z) (threeEquiv_X_zero R)
    · simpa [evaluation] using congrArg (evaluation R x y z) (threeEquiv_X_one R)
    · simpa [evaluation] using congrArg (evaluation R x y z) (threeEquiv_X_two R)

theorem asMvPolynomial_eval (R : Type*) [CommSemiring R] (x y z : R) (P : R[X][X][X]) :
    MvPolynomial.eval ![z, y, x] (asMvPolynomial R P) = (P.map (evalEvalRingHom x y)).eval z := by
  rw [← evaluation_comp_threeEquiv R x y z]
  change evaluation R x y z (threeEquiv R ((threeEquiv R).symm P)) = _
  rw [AlgEquiv.apply_symm_apply, evaluation_apply]

end PaperP1.TrivariatePolynomialEvaluation
