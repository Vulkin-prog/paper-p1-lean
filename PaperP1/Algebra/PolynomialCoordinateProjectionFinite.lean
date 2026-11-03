module

public import PaperP1.Algebra.MonicPolynomialQuotientFinite
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Actual coordinate projections of polynomial quotients with an invertible leading coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialCoordinateProjectionFinite

open MvPolynomial

variable {F : Type*} [Field F] {n : ℕ}

local instance polynomialRing (σ : Type*) : CommRing (MvPolynomial σ F) := inferInstance
local instance polynomialSemiring (σ : Type*) : Semiring (MvPolynomial σ F) :=
  (polynomialRing σ).toSemiring

variable (I : Ideal (MvPolynomial (Fin (n + 1)) F))

def polynomialIdeal : Ideal (Polynomial (MvPolynomial (Fin n) F)) :=
  I.map (finSuccEquiv F n).toRingHom

local instance polynomialQuotientRing : CommRing
    (Polynomial (MvPolynomial (Fin n) F) ⧸ polynomialIdeal I) := inferInstance
local instance polynomialQuotientSemiring : Semiring
    (Polynomial (MvPolynomial (Fin n) F) ⧸ polynomialIdeal I) :=
  (polynomialQuotientRing I).toSemiring

def quotientEquiv : (MvPolynomial (Fin (n + 1)) F ⧸ I) ≃ₐ[F]
    Polynomial (MvPolynomial (Fin n) F) ⧸ polynomialIdeal I :=
  Ideal.quotientEquivAlg I (polynomialIdeal I) (finSuccEquiv F n) rfl

theorem quotientEquiv_mk (p : MvPolynomial (Fin (n + 1)) F) :
    quotientEquiv I (Ideal.Quotient.mk I p) = Ideal.Quotient.mk (polynomialIdeal I) (finSuccEquiv F n p) := rfl

def polynomialParameterMap : MvPolynomial (Fin n) F →ₐ[F]
    Polynomial (MvPolynomial (Fin n) F) ⧸ polynomialIdeal I :=
  (Ideal.Quotient.mkₐ F (polynomialIdeal I)).comp
    (Polynomial.CAlgHom (R := F) (A := MvPolynomial (Fin n) F))

def parameterMap : MvPolynomial (Fin n) F →ₐ[F] (MvPolynomial (Fin (n + 1)) F ⧸ I) :=
  (quotientEquiv I).symm.toAlgHom.comp (polynomialParameterMap I)

theorem parameterMap_X (i : Fin n) :
    parameterMap I (X i) = Ideal.Quotient.mk I (X i.succ) := by
  change (quotientEquiv I).symm (Ideal.Quotient.mk (polynomialIdeal I) (Polynomial.C (X i))) =
    Ideal.Quotient.mk I (X i.succ)
  apply (quotientEquiv I).injective
  rw [AlgEquiv.apply_symm_apply, quotientEquiv_mk, finSuccEquiv_X_succ]

theorem finite (p : MvPolynomial (Fin (n + 1)) F) (hp : p ∈ I)
    (hlc : IsUnit (finSuccEquiv F n p).leadingCoeff) : (parameterMap I).Finite := by
  have hfinite := MonicPolynomialQuotientFinite.of_unit_leadingCoeff_mem (polynomialIdeal I)
    (finSuccEquiv F n p) hlc (Ideal.mem_map_of_mem (finSuccEquiv F n).toRingHom hp)
  have hc : (polynomialParameterMap I).Finite := by
    change (algebraMap (MvPolynomial (Fin n) F)
      (Polynomial (MvPolynomial (Fin n) F) ⧸ polynomialIdeal I)).Finite
    exact RingHom.finite_algebraMap.mpr hfinite
  exact AlgHom.Finite.comp (AlgHom.Finite.of_surjective (quotientEquiv I).symm.toAlgHom
    (quotientEquiv I).symm.surjective) hc

end PaperP1.PolynomialCoordinateProjectionFinite
