module

public import PaperP1.Analysis.BiquadraticAuxiliaryValue
public import PaperP1.Analysis.PrimitiveTailScaling
public import PaperP1.Arithmetic.BiquadraticPrimitiveOrder
public import PaperP1.Arithmetic.BiquadraticNumeratorBounds

/-! # The actual primitive auxiliary is bounded by (B+1)^(400q)/N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticAuxiliaryGap

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.BiquadraticAuxiliaryCoordinates PaperP1.BiquadraticRungeMatrix
  PaperP1.BiquadraticCoefficientPolynomials PaperP1.BiquadraticFormalNumerator
  PaperP1.BiquadraticNumeratorFactor PaperP1.BiquadraticAuxiliaryValue

theorem primitive_bound {q : ℕ} {r s : Fin 3 → ℕ} (B : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (w : CoefficientIndex q r s → ℤ) (D : ℤ[X][X]) (Q : Fin 4 → ℤ[X][X])
    (hD : D ≠ 0) (hfactor : ∀ χ, family w χ = D * Q χ)
    (hDdeg : degreeX D ≤ 3 * q ∧ degreeY D ≤ 3 * q)
    (hQdeg : ∀ χ, degreeX (Q χ) ≤ (3 * q - degreeX D) - blockRank r χ ∧
      degreeY (Q χ) ≤ (3 * q - degreeY D) - blockRank s χ)
    (hQheight : ∀ χ, BivariateHeight.height (Q χ) ≤ (B + 1) ^ (275 * q))
    (γ : (χ : Fin 4) → Fin (2 * blockRank r χ) → ℤ)
    (δ : (χ : Fin 4) → Fin (2 * blockRank s χ) → ℤ)
    (hγ : ∀ χ i, |γ χ i| ≤ (B : ℤ)) (hδ : ∀ χ i, |δ χ i| ≤ (B : ℤ))
    (hzero : ∀ a b, a + b ≤ 6 * q → coefficient a b (numerator γ δ w) = 0)
    (N x y : ℝ) (hN : 8 * (B : ℝ) ≤ N)
    (hx : N ≤ x) (hy : N ≤ y) (hx₂ : x ≤ 2 * N) (hy₂ : y ≤ 2 * N) :
    ‖auxiliaryValue Q γ δ x y‖ ≤ ((B : ℝ) + 1) ^ (400 * q) / N := by
  let kx := 3 * q - degreeX D
  let ky := 3 * q - degreeY D
  let M := kx + ky + totalDegree D + 1
  let f := fromPolynomials Q kx ky γ δ
  have hcoefficient : ∀ a b, |(coefficient a b f : ℝ)| ≤
      ((B : ℝ) + 1) ^ (300 * q) * (2 * (B : ℝ)) ^ (a + b) := by
    intro a b
    have hp := BiquadraticNumeratorBounds.geometric_bound Q kx ky B q hq hqB
      (Nat.sub_le _ _) (Nat.sub_le _ _) hr hs hQdeg hQheight γ δ hγ hδ a b
    exact_mod_cast hp
  have hdiv := BiquadraticPrimitiveOrder.divided_vanishing γ δ w D Q hD hfactor hDdeg.1 hDdeg.2 hzero
  have hfzero : ∀ a b, a + b < M → coefficient a b f = 0 := by
    intro a b hab
    exact hdiv a b (by change a + b < kx + ky + totalDegree D + 1 at hab; omega)
  have hM := PrimitiveTailScaling.remaining_order_budget D q hDdeg.1 hDdeg.2
  have hscaled := PrimitiveTailScaling.scaled_series_bound f B q kx ky M N x y hq hqB
    (Nat.sub_le _ _) (Nat.sub_le _ _) hM.1 hM.2 hN hx hy hx₂ hy₂ hcoefficient hfzero
  have hB : (1 : ℝ) ≤ B := by exact_mod_cast hq.trans hqB
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := by linarith
  have hγsmall : ∀ χ i, |(γ χ i : ℝ) * (1 / x)| < 1 := by
    intro χ i
    have hp := RungeSeriesValues.small_parameter (γ χ i) B x hxp (by linarith) (hγ χ i)
    linarith
  have hδsmall : ∀ χ i, |(δ χ i : ℝ) * (1 / y)| < 1 := by
    intro χ i
    have hp := RungeSeriesValues.small_parameter (δ χ i) B y hyp (by linarith) (hδ χ i)
    linarith
  have hbudget : ∀ χ, Q χ ≠ 0 → blockRank r χ ≤ kx ∧ blockRank s χ ≤ ky := by
    intro χ hχ
    have hp := primitive_pole_budget hr hs w D Q hD hfactor χ hχ
    constructor <;> omega
  have heq := scaled_value Q kx ky hQdeg hbudget γ δ x y hxp.ne' hyp.ne' hγsmall hδsmall
  change ‖x ^ kx * y ^ ky * BivariateSeriesValue.value (fromPolynomials Q kx ky γ δ) (1 / x) (1 / y)‖ ≤ _ at hscaled
  rwa [heq] at hscaled

theorem integer_gap (a N : ℝ) (H : ℝ) (z : ℤ) (ha : a = (z : ℝ))
    (hN : 0 < N) (hH : H < N) (hbound : ‖a‖ ≤ H / N) : a = 0 := by
  have hsmall : |a| < 1 := by
    rw [Real.norm_eq_abs] at hbound
    exact hbound.trans_lt ((div_lt_one hN).mpr hH)
  have hz : |z| < (1 : ℤ) := by rw [ha] at hsmall; exact_mod_cast hsmall
  have hz₀ : z = 0 := by have hh := abs_lt.mp hz; omega
  simp only [ha, hz₀, Int.cast_zero]

end PaperP1.BiquadraticAuxiliaryGap
