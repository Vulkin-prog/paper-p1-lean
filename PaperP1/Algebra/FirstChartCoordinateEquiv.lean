module

public import PaperP1.Algebra.QuadricNormalHomogenization

/-! # Literal changes of free coordinates lifted to the same homogeneous first chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstChartCoordinateEquiv

open MvPolynomial

variable {F : Type*} [CommRing F] {n : ℕ}

theorem finSucc_rename_succ (P : MvPolynomial (Fin n) F) :
    finSuccEquiv F n (rename Fin.succ P) = Polynomial.C P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, rename_X, finSuccEquiv_X_succ, hP]

def liftEquiv (e : MvPolynomial (Fin n) F ≃ₐ[F] MvPolynomial (Fin n) F) :
    MvPolynomial (Fin (n + 1)) F ≃ₐ[F] MvPolynomial (Fin (n + 1)) F :=
  (finSuccEquiv F n).trans ((Polynomial.mapAlgEquiv e).trans (finSuccEquiv F n).symm)

theorem lift_rename_succ (e : MvPolynomial (Fin n) F ≃ₐ[F] MvPolynomial (Fin n) F)
    (P : MvPolynomial (Fin n) F) :
    liftEquiv e (rename Fin.succ P) = rename Fin.succ (e P) := by
  apply (finSuccEquiv F n).injective
  simp only [liftEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    finSucc_rename_succ, Polynomial.coe_mapAlgEquiv, Polynomial.map_C]
  rfl

theorem lift_X_zero (e : MvPolynomial (Fin n) F ≃ₐ[F] MvPolynomial (Fin n) F) :
    liftEquiv e (X 0) = X 0 := by
  apply (finSuccEquiv F n).injective
  simp only [liftEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    finSuccEquiv_X_zero, Polynomial.coe_mapAlgEquiv, Polynomial.map_X]

theorem lift_quadric {F : Type*} [Field F]
    (e : MvPolynomial (Fin 3) F ≃ₐ[F] MvPolynomial (Fin 3) F)
    (L Q : MvPolynomial (Fin 3) F) :
    liftEquiv e (QuadricNormalHomogenization.polynomial L Q) =
      QuadricNormalHomogenization.polynomial (e L) (e Q) := by
  simp only [QuadricNormalHomogenization.polynomial, map_add, map_mul,
    lift_rename_succ, lift_X_zero]

end PaperP1.FirstChartCoordinateEquiv
