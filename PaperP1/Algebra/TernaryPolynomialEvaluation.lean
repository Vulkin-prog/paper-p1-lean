module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Evaluation of an actual polynomial in three successive variables -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPolynomialEvaluation

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def evaluation (a b c : R) : R[X][X][X] →+* R :=
  Polynomial.eval₂RingHom (Polynomial.evalEvalRingHom a b) c

theorem map_coefficients (φ : R →+* S) (P : R[X][X][X]) (a b c : R) :
    evaluation (φ a) (φ b) (φ c)
      (P.map (Polynomial.mapRingHom (Polynomial.mapRingHom φ))) =
      φ (evaluation a b c P) := by
  have he : (evaluation (φ a) (φ b) (φ c)).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Polynomial.mapRingHom φ))) =
      φ.comp (evaluation a b c) := by
    ext <;> simp [evaluation, RingHom.comp_apply]
  exact RingHom.congr_fun he P

theorem quotient_evaluation_eq (I : Ideal R) (P : R[X][X][X]) (a b c x y z : R)
    (hx : x - a ∈ I) (hy : y - b ∈ I) (hz : z - c ∈ I) :
    Ideal.Quotient.mk I (evaluation x y z P) =
      Ideal.Quotient.mk I (evaluation a b c P) := by
  let φ := Ideal.Quotient.mk I
  have hxq : φ x = φ a := Ideal.Quotient.eq.mpr hx
  have hyq : φ y = φ b := Ideal.Quotient.eq.mpr hy
  have hzq : φ z = φ c := Ideal.Quotient.eq.mpr hz
  have he : φ.comp (evaluation x y z) = φ.comp (evaluation a b c) := by
    ext <;> simp [evaluation, RingHom.comp_apply, hxq, hyq, hzq]
  exact RingHom.congr_fun he P

end PaperP1.TernaryPolynomialEvaluation
