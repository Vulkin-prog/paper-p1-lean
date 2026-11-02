module

public import PaperP1.Arithmetic.BiquadraticAuxiliaryConstruction
public import PaperP1.Algebra.BivariateDivisionBounds

/-! # Actual primitive integer coefficient polynomials with explicit quotient height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticPrimitiveCoefficients

open Polynomial PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.BiquadraticFormalNumerator
  PaperP1.BivariateDegrees PaperP1.BivariateDivisionBounds

theorem exists_primitive_coefficients {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, ∃ D : ℤ[X][X], ∃ Q : Fin 4 → ℤ[X][X],
      D ≠ 0 ∧ (∀ χ, family w χ = D * Q χ) ∧
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧
      (∃ χ, Q χ ≠ 0) ∧ (degreeX D ≤ 3 * q ∧ degreeY D ≤ 3 * q) ∧
      (∀ χ, degreeX (Q χ) ≤ (3 * q - blockRank r χ) - degreeX D ∧
        degreeY (Q χ) ≤ (3 * q - blockRank s χ) - degreeY D) ∧
      (∀ χ, BivariateHeight.height (Q χ) ≤ (B + 1) ^ (275 * q)) ∧
      ∀ a b : ℕ, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0 := by
  obtain ⟨w, _hw, _hheight, hfamily, hdegrees, hcoeff, hzero⟩ :=
    BiquadraticAuxiliaryConstruction.exists_auxiliary B hq hqB hr hs γ δ hγ hδ
  obtain ⟨D, Q, hD, hfactor, hprimitive⟩ := PrimitiveCoefficientFamily.extract (family w) hfamily
  obtain ⟨χ, hχ⟩ := hfamily
  have hprod : D * Q χ ≠ 0 := by rwa [← hfactor χ]
  have hQ : Q χ ≠ 0 := right_ne_zero_of_mul hprod
  have hDdegrees : degreeX D ≤ 3 * q ∧ degreeY D ≤ 3 * q := by
    have hd := factor_partial_degrees_le D (Q χ) hprod
    rw [← hfactor χ] at hd
    exact ⟨hd.1.trans ((hdegrees χ).1.trans (Nat.sub_le _ _)),
      hd.2.trans ((hdegrees χ).2.trans (Nat.sub_le _ _))⟩
  refine ⟨w, D, Q, hD, hfactor, hprimitive, ⟨χ, hQ⟩, hDdegrees, ?_, ?_, hzero⟩
  · intro χ
    have hd := quotient_degrees (family w χ) D (Q χ) hD (hfactor χ)
    exact ⟨hd.1.trans (Nat.sub_le_sub_right (hdegrees χ).1 _),
      hd.2.trans (Nat.sub_le_sub_right (hdegrees χ).2 _)⟩
  · intro χ
    have hH : BivariateHeight.height (family w χ) ≤ (B + 1) ^ (266 * q) :=
      height_of_coefficients _ _ (fun i j ↦ hcoeff χ j i)
    exact quotient_height_power (family w χ) D (Q χ) hD (hfactor χ) B q 266 hq hqB
      ((hdegrees χ).1.trans (Nat.sub_le _ _)) ((hdegrees χ).2.trans (Nat.sub_le _ _)) hH

end PaperP1.BiquadraticPrimitiveCoefficients
