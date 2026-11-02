module

public import PaperP1.Analysis.BivariateReciprocalValue
public import PaperP1.Arithmetic.BiquadraticPrimitiveCoefficients

/-! # The literal scaled numerator value is the actual four-polynomial auxiliary -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticAuxiliaryValue

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticRungeMatrix PaperP1.BiquadraticAuxiliaryCoordinates
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.BiquadraticNumeratorFactor
  PaperP1.BivariateSeriesValue PaperP1.BivariateSeriesOperations PaperP1.BivariateReciprocalValue

theorem primitive_pole_budget {q : ℕ} {r s : Fin 3 → ℕ}
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (w : CoefficientIndex q r s → ℤ) (D : ℤ[X][X]) (Q : Fin 4 → ℤ[X][X])
    (hD : D ≠ 0) (hfactor : ∀ χ, family w χ = D * Q χ) (χ : Fin 4) (hQ : Q χ ≠ 0) :
    degreeX (Q χ) + blockRank r χ ≤ 3 * q - degreeX D ∧
      degreeY (Q χ) + blockRank s χ ≤ 3 * q - degreeY D := by
  have hprod := mul_ne_zero hD hQ
  have hDdeg := factor_partial_degrees_le D (Q χ) hprod
  rw [← hfactor χ] at hDdeg
  have hAdeg := family_degrees w χ
  have hQdeg := BivariateDivisionBounds.quotient_degrees (family w χ) D (Q χ) hD (hfactor χ)
  have hrχ := rank_bound q r hr χ
  have hsχ := rank_bound q s hs χ
  constructor <;> omega

def auxiliaryValue {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X])
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) (x y : ℝ) : ℝ :=
  ∑ χ : Fin 4, BivariateEvaluation.evaluate x y (A χ) *
    (x ^ blockRank r χ * y ^ blockRank s χ * value (branch (γ χ) (δ χ)) (1 / x) (1 / y))

theorem zero_value (ξ η : ℝ) : value (0 : Series) ξ η = 0 := by
  simp [value, diagonal, term, coefficient]

theorem fromPolynomials_summable {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X]) (kx ky : ℕ)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) (ξ η : ℝ)
    (hγ : ∀ χ i, |(γ χ i : ℝ) * ξ| < 1) (hδ : ∀ χ i, |(δ χ i : ℝ) * η| < 1) :
    AbsolutelySummable (fromPolynomials A kx ky γ δ) ξ η := by
  unfold fromPolynomials
  apply absolutelySummable_sum
  intro χ _
  exact reciprocal_branch_summable (γ χ) (δ χ) (A χ) _ _ ξ η (hγ χ) (hδ χ)

theorem scaled_value {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X]) (kx ky : ℕ)
    (hA : ∀ χ, degreeX (A χ) ≤ kx - blockRank r χ ∧ degreeY (A χ) ≤ ky - blockRank s χ)
    (hbudget : ∀ χ, A χ ≠ 0 → blockRank r χ ≤ kx ∧ blockRank s χ ≤ ky)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hγ : ∀ χ i, |(γ χ i : ℝ) * (1 / x)| < 1) (hδ : ∀ χ i, |(δ χ i : ℝ) * (1 / y)| < 1) :
    x ^ kx * y ^ ky * value (fromPolynomials A kx ky γ δ) (1 / x) (1 / y) = auxiliaryValue A γ δ x y := by
  unfold fromPolynomials auxiliaryValue
  rw [value_sum univ _ (1 / x) (1 / y)
    (fun χ _ ↦ reciprocal_branch_summable (γ χ) (δ χ) (A χ) _ _ _ _ (hγ χ) (hδ χ)), mul_sum]
  apply sum_congr rfl
  intro χ _
  by_cases hzero : A χ = 0
  · simp only [hzero, BivariateReciprocalSeries.reciprocal_zero, zero_mul, zero_value, map_zero]
    ring
  · obtain ⟨hr, hs⟩ := hbudget χ hzero
    have hxpow : x ^ kx = x ^ blockRank r χ * x ^ (kx - blockRank r χ) := by
      rw [← pow_add]
      congr 1
      omega
    have hypow : y ^ ky = y ^ blockRank s χ * y ^ (ky - blockRank s χ) := by
      rw [← pow_add]
      congr 1
      omega
    have hscaled := scaled_reciprocal_branch (γ χ) (δ χ) (A χ) _ _ (hA χ).1 (hA χ).2 x y hx hy (hγ χ) (hδ χ)
    calc
      _ = (x ^ blockRank r χ * y ^ blockRank s χ) *
          (x ^ (kx - blockRank r χ) * y ^ (ky - blockRank s χ) *
            value (BivariateReciprocalSeries.reciprocal (A χ) (kx - blockRank r χ) (ky - blockRank s χ) *
              branch (γ χ) (δ χ)) (1 / x) (1 / y)) := by rw [hxpow, hypow]; ring
      _ = _ := by rw [hscaled]; ring

end PaperP1.BiquadraticAuxiliaryValue
