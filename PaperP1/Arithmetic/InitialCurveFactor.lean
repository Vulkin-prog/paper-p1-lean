module

public import PaperP1.Algebra.IrreduciblePointFactor
public import PaperP1.Algebra.BivariateLargeRoot
public import PaperP1.Algebra.BivariateDivisionBounds
public import PaperP1.Algebra.BivariateTotalDegree

/-! # Constructing the first irreducible curve through a large integer point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InitialCurveFactor

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.BivariateTotalDegree

theorem exists_curve (P : ℤ[X][X]) (hP : P ≠ 0) (x y : ℤ) (hz : P.evalEval x y = 0)
    (B q c d : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hxdeg : degreeX P ≤ d * q) (hydeg : degreeY P ≤ d * q)
    (hheight : height P ≤ (B + 1) ^ (c * q))
    (hx : (B + 1) ^ ((c + 3 * d) * q) < x.natAbs)
    (hy : (B + 1) ^ ((c + 3 * d) * q) < y.natAbs) :
    ∃ C₀ : ℤ[X][X], Irreducible C₀ ∧ C₀.IsPrimitive ∧
      (∀ n : ℤ, C (C n) ∣ C₀ → IsUnit n) ∧ C₀ ∣ P ∧ C₀.evalEval x y = 0 ∧
      0 < degreeX C₀ ∧ 0 < degreeY C₀ ∧ degreeX C₀ ≤ d * q ∧ degreeY C₀ ≤ d * q ∧
      totalDegree C₀ ≤ 2 * d * q ∧ height C₀ ≤ (B + 1) ^ ((c + 3 * d) * q) := by
  obtain ⟨C₀, hC, hdiv, hzero⟩ := IrreduciblePointFactor.integer_point P hP x y hz
  obtain ⟨D, hD⟩ := hdiv
  have hprod : C₀ * D ≠ 0 := hD ▸ hP
  have hDne : D ≠ 0 := right_ne_zero_of_mul hprod
  have hfactor : P = D * C₀ := by rw [hD, mul_comm]
  have hH := BivariateDivisionBounds.quotient_height_power_general P D C₀ hDne hfactor
    B q c d hq hqB hxdeg hydeg hheight
  have hpositive := BivariateLargeRoot.both_degrees_pos C₀ hC.ne_zero x y hzero (hH.trans_lt hx) (hH.trans_lt hy)
  have hprimitive : C₀.IsPrimitive := hC.isPrimitive (by change C₀.natDegree ≠ 0; exact ne_of_gt hpositive.2)
  have hdegrees := IrreduciblePointFactor.factor_partial_degrees P C₀ hP ⟨D, hD⟩
  have hdx : degreeX C₀ ≤ d * q := hdegrees.1.trans hxdeg
  have hdy : degreeY C₀ ≤ d * q := hdegrees.2.trans hydeg
  have htotal : totalDegree C₀ ≤ 2 * d * q := by
    calc
      _ ≤ degreeX C₀ + degreeY C₀ := totalDegree_le_partial C₀
      _ ≤ d * q + d * q := Nat.add_le_add hdx hdy
      _ = _ := by ring
  exact ⟨C₀, hC, hprimitive, fun n hn ↦ isUnit_C.mp (hprimitive (C n) hn), ⟨D, hD⟩,
    hzero, hpositive.1, hpositive.2, hdx, hdy, htotal, hH⟩

end PaperP1.InitialCurveFactor
