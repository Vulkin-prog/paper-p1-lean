module

public import PaperP1.Algebra.BivariateFactorHeight
public import PaperP1.Algebra.PrimitiveCoefficientFamily
public import Mathlib.Tactic.Positivity

/-! # Dividing by a common integer polynomial retains explicit degree and height budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateDivisionBounds

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight

theorem quotient_degrees (P D Q : ℤ[X][X]) (hD : D ≠ 0) (hfactor : P = D * Q) :
    degreeX Q ≤ degreeX P - degreeX D ∧ degreeY Q ≤ degreeY P - degreeY D := by
  by_cases hQ : Q = 0
  · simp only [hQ, degreeX, map_zero, degreeY, natDegree_zero, Nat.zero_le, and_self]
  · have hsD : Bivariate.swap D ≠ 0 := by
      intro h
      exact hD ((Bivariate.swap (R := ℤ)).injective (h.trans (map_zero _).symm))
    have hsQ : Bivariate.swap Q ≠ 0 := by
      intro h
      exact hQ ((Bivariate.swap (R := ℤ)).injective (h.trans (map_zero _).symm))
    have hx : degreeX P = degreeX D + degreeX Q := by
      rw [hfactor, degreeX, map_mul, natDegree_mul hsD hsQ]
      rfl
    have hy : degreeY P = degreeY D + degreeY Q := by
      rw [hfactor, degreeY, natDegree_mul hD hQ]
      rfl
    omega

theorem height_of_coefficients (P : ℤ[X][X]) (H : ℕ)
    (hcoeff : ∀ i j, |(P.coeff i).coeff j| ≤ (H : ℤ)) : height P ≤ H := by
  unfold height PaperP1.integerPolynomialHeight
  apply Finset.sup_le
  intro i _
  apply Finset.sup_le
  intro j _
  have h : (((P.coeff i).coeff j).natAbs : ℤ) ≤ (H : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using hcoeff i j
  exact_mod_cast h

theorem quotient_height (P D Q : ℤ[X][X]) (hD : D ≠ 0) (hfactor : P = D * Q)
    (KX KY H : ℕ) (hx : degreeX P ≤ KX) (hy : degreeY P ≤ KY) (hH : height P ≤ H) :
    (height Q : ℝ) ≤ (2 : ℝ) ^ (KX + KY) *
      Real.sqrt (((KX + 1) * (KY + 1) : ℕ) : ℝ) * H := by
  by_cases hQ : Q = 0
  · simp only [hQ, height, support_zero, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero]
    positivity
  · have hP : P ≠ 0 := hfactor ▸ mul_ne_zero hD hQ
    have hf := BivariateFactorHeight.companion_T9_4_factor_and_quotient P D Q hP hfactor
    have hp : (2 : ℝ) ^ (degreeX P + degreeY P) ≤ (2 : ℝ) ^ (KX + KY) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add hx hy)
    have hs : Real.sqrt (((degreeX P + 1) * (degreeY P + 1) : ℕ) : ℝ) ≤
        Real.sqrt (((KX + 1) * (KY + 1) : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.mul_le_mul (Nat.add_le_add_right hx 1) (Nat.add_le_add_right hy 1)
    have hm := mul_le_mul hp hs (Real.sqrt_nonneg _) (by positivity)
    exact (hf.2.1.trans hf.2.2).trans (mul_le_mul hm (by exact_mod_cast hH) (Nat.cast_nonneg _) (by positivity))

theorem linear_dimension_power (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B) :
    3 * q + 1 ≤ (B + 1) ^ (3 * q) := by
  have hB : 1 ≤ B := hq.trans hqB
  have hfour : 4 ≤ (B + 1) ^ 2 :=
    (by norm_num : 4 ≤ (2 : ℕ) ^ 2).trans (Nat.pow_le_pow_left (by omega : 2 ≤ B + 1) 2)
  calc
    _ ≤ 4 * B := by omega
    _ ≤ (B + 1) ^ 2 * (B + 1) := Nat.mul_le_mul hfour (Nat.le_succ B)
    _ = (B + 1) ^ 3 := (pow_succ _ 2).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < B + 1) (by omega)

theorem quotient_height_power (P D Q : ℤ[X][X]) (hD : D ≠ 0) (hfactor : P = D * Q)
    (B q c : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hx : degreeX P ≤ 3 * q) (hy : degreeY P ≤ 3 * q) (hH : height P ≤ (B + 1) ^ (c * q)) :
    height Q ≤ (B + 1) ^ ((c + 9) * q) := by
  have hB : 1 ≤ B := hq.trans hqB
  have hbase : (2 : ℝ) ≤ B + 1 := by exact_mod_cast (show 2 ≤ B + 1 by omega)
  have hsqrt : Real.sqrt (((3 * q + 1) * (3 * q + 1) : ℕ) : ℝ) = (3 * q + 1 : ℕ) := by
    rw [show (((3 * q + 1) * (3 * q + 1) : ℕ) : ℝ) = (((3 * q + 1 : ℕ) : ℝ) ^ 2) by push_cast; ring,
      Real.sqrt_sq (by positivity)]
  have hlinear : ((3 * q + 1 : ℕ) : ℝ) ≤ ((B : ℝ) + 1) ^ (3 * q) := by
    exact_mod_cast linear_dimension_power B q hq hqB
  have hp : (2 : ℝ) ^ (6 * q) ≤ ((B : ℝ) + 1) ^ (6 * q) :=
    pow_le_pow_left₀ (by norm_num) hbase _
  have hfinite := quotient_height P D Q hD hfactor (3 * q) (3 * q) ((B + 1) ^ (c * q)) hx hy hH
  rw [hsqrt, show 3 * q + 3 * q = 6 * q by omega] at hfinite
  have hbound : (height Q : ℝ) ≤ ((B : ℝ) + 1) ^ ((c + 9) * q) := by
    calc
      _ ≤ (2 : ℝ) ^ (6 * q) * ((3 * q + 1 : ℕ) : ℝ) * ((B + 1) ^ (c * q) : ℕ) := hfinite
      _ ≤ (((B : ℝ) + 1) ^ (6 * q) * ((B : ℝ) + 1) ^ (3 * q)) * ((B + 1) ^ (c * q) : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hp hlinear (by positivity) (by positivity)) (Nat.cast_nonneg _)
      _ = _ := by push_cast; rw [← pow_add, ← pow_add]; congr 1; ring
  exact_mod_cast hbound

theorem quotient_height_power_general (P D Q : ℤ[X][X]) (hD : D ≠ 0) (hfactor : P = D * Q)
    (B q c d : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hx : degreeX P ≤ d * q) (hy : degreeY P ≤ d * q) (hH : height P ≤ (B + 1) ^ (c * q)) :
    height Q ≤ (B + 1) ^ ((c + 3 * d) * q) := by
  have hbase : (2 : ℝ) ≤ B + 1 := by exact_mod_cast (show 2 ≤ B + 1 by omega)
  have hsqrt : Real.sqrt (((d * q + 1) * (d * q + 1) : ℕ) : ℝ) = (d * q + 1 : ℕ) := by
    rw [show (((d * q + 1) * (d * q + 1) : ℕ) : ℝ) = (((d * q + 1 : ℕ) : ℝ) ^ 2) by push_cast; ring,
      Real.sqrt_sq (by positivity)]
  have hlinear : ((d * q + 1 : ℕ) : ℝ) ≤ ((B : ℝ) + 1) ^ (d * q) := by
    have hn : d * q + 1 ≤ (B + 1) ^ (d * q) :=
      (Nat.succ_le_of_lt (show d * q < 2 ^ (d * q) from Nat.lt_two_pow_self)).trans
        (Nat.pow_le_pow_left (by omega : 2 ≤ B + 1) _)
    exact_mod_cast hn
  have hp : (2 : ℝ) ^ (2 * d * q) ≤ ((B : ℝ) + 1) ^ (2 * d * q) :=
    pow_le_pow_left₀ (by norm_num) hbase _
  have hfinite := quotient_height P D Q hD hfactor (d * q) (d * q) ((B + 1) ^ (c * q)) hx hy hH
  rw [hsqrt, show d * q + d * q = 2 * d * q by ring] at hfinite
  have hbound : (height Q : ℝ) ≤ ((B : ℝ) + 1) ^ ((c + 3 * d) * q) := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * d * q) * ((d * q + 1 : ℕ) : ℝ) * ((B + 1) ^ (c * q) : ℕ) := hfinite
      _ ≤ (((B : ℝ) + 1) ^ (2 * d * q) * ((B : ℝ) + 1) ^ (d * q)) * ((B + 1) ^ (c * q) : ℕ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hp hlinear (by positivity) (by positivity)) (Nat.cast_nonneg _)
      _ = _ := by push_cast; rw [← pow_add, ← pow_add]; congr 1; ring
  exact_mod_cast hbound

end PaperP1.BivariateDivisionBounds
