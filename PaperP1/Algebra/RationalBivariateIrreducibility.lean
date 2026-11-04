module

public import PaperP1.Algebra.IntegerBivariateFactorCover
public import PaperP1.Algebra.RationalMultivariatePrime
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Actual nonconstant integer irreducible bivariate factors are irreducible over the rationals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalBivariateIrreducibility

open Polynomial PaperP1.IntegerBivariateFactorCover

def rationalize (G : ℤ[X][X]) : ℚ[X][X] := G.map (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem map_naturality (G : ℤ[X][X]) :
    Bivariate.equivMvPolynomial ℚ (rationalize G) =
      MvPolynomial.map (Int.castRingHom ℚ) (Bivariate.equivMvPolynomial ℤ G) := by
  let eZ := Bivariate.equivMvPolynomial ℤ
  let eQ := Bivariate.equivMvPolynomial ℚ
  let φ := Int.castRingHom ℚ
  let m := Polynomial.mapRingHom (Polynomial.mapRingHom φ)
  have hh : eQ.toRingHom.comp m = (MvPolynomial.map φ).comp eZ.toRingHom := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro z
        simp [m, eZ, eQ, φ]
      · simp [m, eZ, eQ, φ]
    · simp [m, eZ, eQ, φ]
  exact congrArg (fun f : ℤ[X][X] →+* MvPolynomial (Fin 2) ℚ ↦ f G) hh

theorem nonconstant_of_degreeSum_pos (G : ℤ[X][X]) (hG : 0 < degreeSum G) :
    ∀ z : ℤ, Bivariate.equivMvPolynomial ℤ G ≠ MvPolynomial.C z := by
  intro z hz
  have hc : G = Polynomial.C (Polynomial.C z) := by
    have hh := congrArg (Bivariate.equivMvPolynomial ℤ).symm hz
    simpa only [AlgEquiv.symm_apply_apply, Bivariate.equivMvPolynomial_symm_C] using hh
  have hd : degreeSum G = 0 := by
    rw [hc]
    simp [degreeSum, PaperP1.BivariateDegrees.degreeX, PaperP1.BivariateDegrees.degreeY]
  omega

theorem rational_irreducible (G : ℤ[X][X]) (hG : Irreducible G) (hdegree : 0 < degreeSum G) :
    Irreducible (rationalize G) := by
  have hp : Prime G := irreducible_iff_prime.mp hG
  have hpm : Prime (Bivariate.equivMvPolynomial ℤ G) := (MulEquiv.prime_iff (Bivariate.equivMvPolynomial ℤ)).mpr hp
  have hq := RationalMultivariatePrime.prime_map (Bivariate.equivMvPolynomial ℤ G) hpm (nonconstant_of_degreeSum_pos G hdegree)
  have hirr : Irreducible (Bivariate.equivMvPolynomial ℚ (rationalize G)) := by
    rw [map_naturality]
    exact hq.irreducible
  exact (MulEquiv.irreducible_iff (Bivariate.equivMvPolynomial ℚ)).mp hirr

end PaperP1.RationalBivariateIrreducibility
