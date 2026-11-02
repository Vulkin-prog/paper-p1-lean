module

public import PaperP1.Algebra.BivariateReciprocalProduct
public import PaperP1.Arithmetic.BiquadraticPrimitiveCoefficients

/-! # The actual auxiliary numerator factors by the reciprocal common polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticNumeratorFactor

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateReciprocalSeries
  PaperP1.BivariateReciprocalProduct PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.BiquadraticAuxiliaryCoordinates
  PaperP1.BiquadraticRungeMatrix

theorem reciprocal_rectangle (a b : ℕ) (w : Fin (a + 1) × Fin (b + 1) → ℤ) :
    reciprocal (rectangle a b w) a b = ∑ i : Fin (a + 1) × Fin (b + 1),
      PowerSeries.C (PowerSeries.C (w i : ℚ)) *
        (PowerSeries.C (PowerSeries.X : PowerSeries ℚ) ^ (a - i.1.val) *
          (PowerSeries.X : Series) ^ (b - i.2.val)) := by
  rw [reciprocal_sum]
  apply sum_congr rfl
  intro i _
  rw [rectangle_coefficient]

theorem reciprocal_rectangle_mul (a b : ℕ) (w : Fin (a + 1) × Fin (b + 1) → ℤ) (f : Series) :
    reciprocal (rectangle a b w) a b * f =
      ∑ i : Fin (a + 1) × Fin (b + 1),
        PowerSeries.C (PowerSeries.C (w i : ℚ)) * shift (a - i.1.val) (b - i.2.val) f := by
  rw [reciprocal_rectangle, sum_mul]
  apply sum_congr rfl
  intro i _
  unfold shift
  rw [map_pow]
  ring

def fromPolynomials {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X]) (kx ky : ℕ)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) : Series :=
  ∑ χ : Fin 4, reciprocal (A χ) (kx - blockRank r χ) (ky - blockRank s χ) *
    branch (γ χ) (δ χ)

theorem numerator_eq_family {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (w : CoefficientIndex q r s → ℤ) :
    numerator γ δ w = fromPolynomials (family w) (3 * q) (3 * q) γ δ := by
  unfold numerator fromPolynomials
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  conv_rhs => rw [Fin.sum_univ_succ]
  congr 1
  · change _ = reciprocal (rectangle (3 * q) (3 * q) (fun p ↦ w (.inl p)))
      (3 * q) (3 * q) * branch (γ 0) (δ 0)
    rw [reciprocal_rectangle_mul]
    rfl
  · apply sum_congr rfl
    intro j _
    change _ = reciprocal
      (rectangle (3 * q - r j) (3 * q - s j) (fun p ↦ w (.inr ⟨j, p⟩)))
      (3 * q - r j) (3 * q - s j) * branch (γ j.succ) (δ j.succ)
    rw [reciprocal_rectangle_mul]
    rfl

theorem reciprocal_factor (D Q : ℤ[X][X]) (a b : ℕ) (hD : D ≠ 0)
    (hx : degreeX (D * Q) ≤ a) (hy : degreeY (D * Q) ≤ b) :
    reciprocal (D * Q) a b = reciprocal D (degreeX D) (degreeY D) *
      reciprocal Q (a - degreeX D) (b - degreeY D) := by
  by_cases hQ : Q = 0
  · simp only [hQ, mul_zero, reciprocal_zero]
  · have hprod : D * Q ≠ 0 := mul_ne_zero hD hQ
    have hd := factor_partial_degrees_le D Q hprod
    have hdx : degreeX D ≤ a := hd.1.trans hx
    have hdy : degreeY D ≤ b := hd.2.trans hy
    have hquot := BivariateDivisionBounds.quotient_degrees (D * Q) D Q hD rfl
    have hqx := hquot.1.trans (Nat.sub_le_sub_right hx _)
    have hqy := hquot.2.trans (Nat.sub_le_sub_right hy _)
    have h := reciprocal_mul D Q (degreeX D) (degreeY D)
      (a - degreeX D) (b - degreeY D) le_rfl le_rfl hqx hqy
    simpa only [Nat.add_sub_of_le hdx, Nat.add_sub_of_le hdy] using h

theorem fromPolynomials_factor {r s : Fin 3 → ℕ} (A : Fin 4 → ℤ[X][X])
    (D : ℤ[X][X]) (Q : Fin 4 → ℤ[X][X]) (kx ky : ℕ) (hD : D ≠ 0)
    (hfactor : ∀ χ, A χ = D * Q χ)
    (hdegrees : ∀ χ, degreeX (A χ) ≤ kx - blockRank r χ ∧
      degreeY (A χ) ≤ ky - blockRank s χ)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ) :
    fromPolynomials A kx ky γ δ = reciprocal D (degreeX D) (degreeY D) *
      fromPolynomials Q (kx - degreeX D) (ky - degreeY D) γ δ := by
  unfold fromPolynomials
  rw [mul_sum]
  apply sum_congr rfl
  intro χ _
  have hx := (hdegrees χ).1
  have hy := (hdegrees χ).2
  rw [hfactor χ] at hx hy ⊢
  rw [reciprocal_factor D (Q χ) _ _ hD hx hy]
  have heX : (kx - blockRank r χ) - degreeX D = (kx - degreeX D) - blockRank r χ := by omega
  have heY : (ky - blockRank s χ) - degreeY D = (ky - degreeY D) - blockRank s χ := by omega
  rw [heX, heY, mul_assoc]

theorem numerator_factor {q : ℕ} {r s : Fin 3 → ℕ}
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (w : CoefficientIndex q r s → ℤ) (D : ℤ[X][X]) (Q : Fin 4 → ℤ[X][X])
    (hD : D ≠ 0) (hfactor : ∀ χ, family w χ = D * Q χ) :
    numerator γ δ w = reciprocal D (degreeX D) (degreeY D) *
      fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ := by
  rw [numerator_eq_family]
  exact fromPolynomials_factor (family w) D Q (3 * q) (3 * q) hD hfactor
    (family_degrees w) γ δ

end PaperP1.BiquadraticNumeratorFactor
