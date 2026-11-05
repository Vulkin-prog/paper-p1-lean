module

public import PaperP1.Algebra.ConicCoordinateChanges
public import PaperP1.Algebra.RationalBivariateIrreducibility

/-! # Rational association preserves the actual conic discriminant sign -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConicScalarInvariants

open Polynomial PaperP1.ConicNormCoordinates PaperP1.ConicPolynomialPresentation
open PaperP1.RationalBivariateIrreducibility

theorem associated_scalar {F : Type*} [Field F] (P Q : F[X][X]) (h : Associated P Q) :
    ∃ s : F, s ≠ 0 ∧ Q = C (C s) * P := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨p, hp, hpu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨s, hs, hsp⟩ := Polynomial.isUnit_iff.mp hp
  refine ⟨s, hs.ne_zero, ?_⟩
  rw [← hu, ← hpu, ← hsp]
  exact mul_comm _ _

theorem coefficient_scalar_mul {F : Type*} [Field F] (P Q : F[X][X]) (s : F)
    (hQ : Q = C (C s) * P) (y x : ℕ) : (Q.coeff y).coeff x = s * (P.coeff y).coeff x := by
  rw [hQ, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]

theorem rationalized_coefficient (P : ℤ[X][X]) (y x : ℕ) :
    ((rationalize P).coeff y).coeff x = ((P.coeff y).coeff x : ℚ) := by
  simp only [rationalize, Polynomial.coeff_map, Polynomial.coe_mapRingHom, Int.coe_castRingHom]

theorem associated_discriminant_scale (P Q : ℤ[X][X]) (h : Associated (rationalize P) (rationalize Q)) :
    ∃ s : ℚ, s ≠ 0 ∧ (discriminant (coefficients Q) : ℚ) =
      s ^ 2 * (discriminant (coefficients P) : ℚ) := by
  obtain ⟨s, hs, hQ⟩ := associated_scalar (rationalize P) (rationalize Q) h
  have hcoeff (y x : ℕ) : ((Q.coeff y).coeff x : ℚ) = s * ((P.coeff y).coeff x : ℚ) := by
    simpa only [rationalized_coefficient] using coefficient_scalar_mul (rationalize P) (rationalize Q) s hQ y x
  refine ⟨s, hs, ?_⟩
  simp only [discriminant, coefficients, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
  rw [hcoeff 1 1, hcoeff 0 2, hcoeff 2 0]
  ring

theorem positive_discriminant_iff (P Q : ℤ[X][X]) (h : Associated (rationalize P) (rationalize Q)) :
    0 < discriminant (coefficients P) ↔ 0 < discriminant (coefficients Q) := by
  obtain ⟨s, hs, hscale⟩ := associated_discriminant_scale P Q h
  have hh : (0 : ℚ) < (discriminant (coefficients Q) : ℚ) ↔
      0 < (discriminant (coefficients P) : ℚ) := by
    rw [hscale, mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hs)]
  exact_mod_cast hh.symm

theorem zero_discriminant_iff (P Q : ℤ[X][X]) (h : Associated (rationalize P) (rationalize Q)) :
    discriminant (coefficients P) = 0 ↔ discriminant (coefficients Q) = 0 := by
  obtain ⟨s, hs, hscale⟩ := associated_discriminant_scale P Q h
  have hh : (discriminant (coefficients Q) : ℚ) = 0 ↔ (discriminant (coefficients P) : ℚ) = 0 := by
    rw [hscale, mul_eq_zero]
    simp only [pow_ne_zero 2 hs, false_or]
  exact_mod_cast hh.symm

theorem negative_discriminant_iff (P Q : ℤ[X][X]) (h : Associated (rationalize P) (rationalize Q)) :
    discriminant (coefficients P) < 0 ↔ discriminant (coefficients Q) < 0 := by
  obtain ⟨s, hs, hscale⟩ := associated_discriminant_scale P Q h
  have hh : (discriminant (coefficients Q) : ℚ) < 0 ↔ (discriminant (coefficients P) : ℚ) < 0 := by
    rw [hscale]
    have hm : s ^ 2 * (discriminant (coefficients P) : ℚ) < s ^ 2 * (0 : ℚ) ↔
        (discriminant (coefficients P) : ℚ) < 0 := mul_lt_mul_iff_right₀ (sq_pos_of_ne_zero hs)
    simpa only [mul_zero] using hm
  exact_mod_cast hh.symm

end PaperP1.ConicScalarInvariants
