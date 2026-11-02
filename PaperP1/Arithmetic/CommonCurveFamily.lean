module

public import PaperP1.Arithmetic.InitialCurveFactor
public import PaperP1.Algebra.BivariateResultantHeight
public import PaperP1.Algebra.BivariateResultantPoint
public import PaperP1.Algebra.ResultantPowerBudget

/-! # One actual irreducible curve for a uniformly bounded polynomial family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonCurveFamily

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.BivariateTotalDegree

theorem linear_threshold (B q : ℕ) (hq : 1 ≤ q) :
    (B + 1) ^ (2472 * q) ≤ (B + 1) ^ (1000000 * q ^ 2) := by
  have hqq : q ≤ q ^ 2 := by simpa only [mul_one, pow_two] using Nat.mul_le_mul_left q hq
  apply Nat.pow_le_pow_right (by omega)
  exact (Nat.mul_le_mul_left 2472 hqq).trans (Nat.mul_le_mul_right _ (by decide : 2472 ≤ 1000000))

theorem exists_curve {ι : Type*} (P : ι → ℤ[X][X]) (i₀ : ι) (hne : P i₀ ≠ 0)
    (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hdegX : ∀ i, degreeX (P i) ≤ 24 * q) (hdegY : ∀ i, degreeY (P i) ≤ 24 * q)
    (hheight : ∀ i, height (P i) ≤ (B + 1) ^ (2400 * q))
    (x y : ℤ) (hpoint : ∀ i, (P i).evalEval x y = 0)
    (hx : (B + 1) ^ (1000000 * q ^ 2) < x.natAbs)
    (hy : (B + 1) ^ (1000000 * q ^ 2) < y.natAbs) :
    ∃ C₀ : ℤ[X][X], Irreducible C₀ ∧ C₀.IsPrimitive ∧
      (∀ n : ℤ, C (C n) ∣ C₀ → IsUnit n) ∧ (∀ i, C₀ ∣ P i) ∧ C₀.evalEval x y = 0 ∧
      0 < degreeX C₀ ∧ 0 < degreeY C₀ ∧ degreeX C₀ ≤ 24 * q ∧ degreeY C₀ ≤ 24 * q ∧
      totalDegree C₀ ≤ 48 * q ∧ height C₀ ≤ (B + 1) ^ (2472 * q) := by
  have hsmallx : (B + 1) ^ ((2400 + 3 * 24) * q) < x.natAbs :=
    (linear_threshold B q hq).trans_lt hx
  have hsmally : (B + 1) ^ ((2400 + 3 * 24) * q) < y.natAbs :=
    (linear_threshold B q hq).trans_lt hy
  obtain ⟨C₀, hC, hprimitive, hIntPrimitive, _hdiv₀, hCpoint, hCx, hCy, hCdx, hCdy, hCtotal, hCH⟩ :=
    InitialCurveFactor.exists_curve (P i₀) hne x y (hpoint i₀) B q 2400 24 hq hqB
      (hdegX i₀) (hdegY i₀) (hheight i₀) hsmallx hsmally
  have hdiv (i : ι) : C₀ ∣ P i := by
    apply BivariateResultantPoint.divides_of_large_point C₀ (P i) hC hCy x y hCpoint (hpoint i)
    have hPi : height (P i) ≤ (B + 1) ^ (2472 * q) :=
      (hheight i).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have hres := BivariateResultantHeight.resultant_height C₀ (P i) C₀.natDegree (P i).natDegree
      (24 * q) ((B + 1) ^ (2472 * q)) hCdx (hdegX i) hCH hPi
    have hn : C₀.natDegree + (P i).natDegree ≤ 48 * q := by
      change degreeY C₀ + degreeY (P i) ≤ 48 * q
      have hi := hdegY i
      omega
    have hbudget := ResultantPowerBudget.common_curve_budget B q (C₀.natDegree + (P i).natDegree)
      (24 * q) ((B + 1) ^ (2472 * q)) hq hqB hn le_rfl le_rfl
    have hpow : (B + 1) ^ (124608 * q ^ 2) ≤ (B + 1) ^ (1000000 * q ^ 2) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by decide : 124608 ≤ 1000000))
    exact ((hres.trans hbudget).trans hpow).trans_lt hx
  exact ⟨C₀, hC, hprimitive, hIntPrimitive, hdiv, hCpoint, hCx, hCy, hCdx, hCdy, hCtotal, hCH⟩

end PaperP1.CommonCurveFamily
