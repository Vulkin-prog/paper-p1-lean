module

public import PaperP1.Arithmetic.BiquadraticNumeratorFactor

/-! # Dividing the actual common factor preserves vanishing beyond the remaining pole weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticPrimitiveOrder

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.BivariateReciprocalSeries PaperP1.BivariateSeriesOrder
  PaperP1.BiquadraticNumeratorFactor PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix
  PaperP1.BiquadraticCoefficientPolynomials

theorem divided_vanishing {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (w : CoefficientIndex q r s → ℤ) (D : ℤ[X][X]) (Q : Fin 4 → ℤ[X][X])
    (hD : D ≠ 0) (hfactor : ∀ χ, family w χ = D * Q χ)
    (hx : degreeX D ≤ 3 * q) (hy : degreeY D ≤ 3 * q)
    (hzero : ∀ a b : ℕ, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0) :
    ∀ a b : ℕ, a + b ≤ (3 * q - degreeX D) + (3 * q - degreeY D) + totalDegree D →
      coefficient a b (fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ) = 0 := by
  have horder := totalOrder_reciprocal D (degreeX D) (degreeY D) hD le_rfl le_rfl
  have hprod : ∀ a b : ℕ, a + b < 6 * q + 1 → coefficient a b
      (reciprocal D (degreeX D) (degreeY D) *
        fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ) = 0 := by
    intro a b hab
    rw [← numerator_factor γ δ w D Q hD hfactor]
    exact hzero a b (by omega)
  have hlow := quotient_vanishing _ _ _ (6 * q + 1) horder hprod
  have he := totalDegree_le_partial D
  intro a b hab
  apply hlow a b
  omega

theorem exists_primitive_vanishing {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, ∃ D : ℤ[X][X], ∃ Q : Fin 4 → ℤ[X][X],
      D ≠ 0 ∧ (∀ χ, family w χ = D * Q χ) ∧
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧
      (∃ χ, Q χ ≠ 0) ∧ (degreeX D ≤ 3 * q ∧ degreeY D ≤ 3 * q) ∧
      (∀ χ, degreeX (Q χ) ≤ (3 * q - degreeX D) - blockRank r χ ∧
        degreeY (Q χ) ≤ (3 * q - degreeY D) - blockRank s χ) ∧
      (∀ χ, BivariateHeight.height (Q χ) ≤ (B + 1) ^ (275 * q)) ∧
      numerator γ δ w = reciprocal D (degreeX D) (degreeY D) *
        fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ ∧
      (∀ a b : ℕ, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0) ∧
      ∀ a b : ℕ, a + b ≤ (3 * q - degreeX D) + (3 * q - degreeY D) + totalDegree D →
        coefficient a b (fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ) = 0 := by
  obtain ⟨w, D, Q, hD, hfactor, hprimitive, hQ, hDdegrees, hdegrees, hheight, hzero⟩ :=
    BiquadraticPrimitiveCoefficients.exists_primitive_coefficients B hq hqB hr hs γ δ hγ hδ
  refine ⟨w, D, Q, hD, hfactor, hprimitive, hQ, hDdegrees, ?_, hheight,
    numerator_factor γ δ w D Q hD hfactor, hzero,
    divided_vanishing γ δ w D Q hD hfactor hDdegrees.1 hDdegrees.2 hzero⟩
  intro χ
  have hdx := (hdegrees χ).1
  have hdy := (hdegrees χ).2
  constructor <;> omega

end PaperP1.BiquadraticPrimitiveOrder
