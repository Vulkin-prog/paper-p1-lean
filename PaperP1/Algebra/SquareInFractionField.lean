module

public import Mathlib.Algebra.Group.Even
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-! # Squares in the fraction field of an integrally closed domain -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.SquareInFractionField

theorem square_reflect {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] (r : R) :
    IsSquare (algebraMap R K r) ↔ IsSquare r := by
  constructor
  · rintro ⟨x, hx⟩
    have hpow : x ^ 2 = algebraMap R K r := by simpa only [pow_two] using hx.symm
    have hint : IsIntegral R (x ^ 2) := hpow ▸ isIntegral_algebraMap
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
      (R := R) (K := K) (by decide : 0 < 2) hint
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective R K
    simpa only [map_mul, hy] using hx
  · exact IsSquare.map (algebraMap R K)

theorem square_mul_square_iff {F : Type*} [Field F] (a b : F) (hb : b ≠ 0) :
    IsSquare (a * b ^ 2) ↔ IsSquare a := by
  constructor
  · intro h
    have hs : IsSquare (b ^ 2) := ⟨b, pow_two b⟩
    simpa only [mul_div_cancel_right₀ a (pow_ne_zero 2 hb)] using h.div hs
  · intro h
    exact h.mul ⟨b, pow_two b⟩

end PaperP1.SquareInFractionField
