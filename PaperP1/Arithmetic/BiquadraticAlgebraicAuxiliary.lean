module

public import PaperP1.Arithmetic.BiquadraticPrimitiveOrder
public import PaperP1.Arithmetic.BiquadraticWordNormHeight

/-! # One actual construction contains primitive coefficients, formal cancellation, and a small nonzero word norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticAlgebraicAuxiliary

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticNumeratorFactor PaperP1.BivariateReciprocalSeries
  PaperP1.BiquadraticWordNorm
open scoped symmDiff

theorem exists_auxiliary {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (I J K L : Finset ℤ) (hind : Independent I J K L)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (hcardx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcardy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ)) :
    ∃ w : CoefficientIndex q r s → ℤ, ∃ D : ℤ[X][X], ∃ Q : Fin 4 → ℤ[X][X], ∃ R : ℤ[X][X],
      D ≠ 0 ∧ (∀ χ, family w χ = D * Q χ) ∧
      (∀ E : ℤ[X][X], (∀ χ, E ∣ Q χ) → IsUnit E) ∧ (∃ χ, Q χ ≠ 0) ∧
      (degreeX D ≤ 3 * q ∧ degreeY D ≤ 3 * q) ∧
      (∀ χ, degreeX (Q χ) ≤ (3 * q - degreeX D) - blockRank r χ ∧
        degreeY (Q χ) ≤ (3 * q - degreeY D) - blockRank s χ) ∧
      (∀ χ, BivariateHeight.height (Q χ) ≤ (B + 1) ^ (275 * q)) ∧
      R = normPolynomial I J K L Q ∧ R ≠ 0 ∧
      (degreeX R ≤ 12 * q ∧ degreeY R ≤ 12 * q ∧ totalDegree R ≤ 24 * q) ∧
      BivariateHeight.height R ≤ (B + 1) ^ (1200 * q) ∧
      numerator γ δ w = reciprocal D (degreeX D) (degreeY D) *
        fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ ∧
      (∀ a b : ℕ, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0) ∧
      ∀ a b : ℕ, a + b ≤ (3 * q - degreeX D) + (3 * q - degreeY D) + totalDegree D →
        coefficient a b (fromPolynomials Q (3 * q - degreeX D) (3 * q - degreeY D) γ δ) = 0 := by
  obtain ⟨w, D, Q, hD, hfactor, hprimitive, hQ, hDdeg, hQdeg, hQheight, hprod, hzero, hdiv⟩ :=
    BiquadraticPrimitiveOrder.exists_primitive_vanishing B hq hqB hr hs γ δ hγ hδ
  have hQorig : ∀ χ, degreeX (Q χ) ≤ 3 * q - blockRank r χ ∧
      degreeY (Q χ) ≤ 3 * q - blockRank s χ := by
    intro χ
    have hx := (hQdeg χ).1
    have hy := (hQdeg χ).2
    constructor <;> omega
  have hQsimple : ∀ χ, degreeX (Q χ) ≤ 3 * q ∧ degreeY (Q χ) ≤ 3 * q := fun χ ↦
    ⟨(hQorig χ).1.trans (Nat.sub_le _ _), (hQorig χ).2.trans (Nat.sub_le _ _)⟩
  have hcx : I.card ≤ 2 * q ∧ K.card ≤ 2 * q ∧ (I ∆ K).card ≤ 2 * q := by
    rw [hcardx.1, hcardx.2.1, hcardx.2.2]
    exact ⟨Nat.mul_le_mul_left 2 (hr 0), Nat.mul_le_mul_left 2 (hr 1), Nat.mul_le_mul_left 2 (hr 2)⟩
  have hcy : J.card ≤ 2 * q ∧ L.card ≤ 2 * q ∧ (J ∆ L).card ≤ 2 * q := by
    rw [hcardy.1, hcardy.2.1, hcardy.2.2]
    exact ⟨Nat.mul_le_mul_left 2 (hs 0), Nat.mul_le_mul_left 2 (hs 1), Nat.mul_le_mul_left 2 (hs 2)⟩
  refine ⟨w, D, Q, normPolynomial I J K L Q, hD, hfactor, hprimitive, hQ, hDdeg, hQdeg, hQheight,
    rfl, normPolynomial_ne_zero I J K L hind Q hQ,
    BiquadraticWordNormDegree.q_bounds I J K L Q q r s hr hs hcardx hcardy hQorig,
    BiquadraticWordNormHeight.height_bound I J K L Q B q hq hqB hI hJ hK hL hcx hcy hQsimple hQheight,
    hprod, hzero, hdiv⟩

end PaperP1.BiquadraticAlgebraicAuxiliary
