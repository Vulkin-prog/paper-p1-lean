module

public import PaperP1.Arithmetic.WidePlaneInterpolation
public import PaperP1.Algebra.BivariateDivisionBounds
public import PaperP1.Algebra.BivariateCurveDegrees

/-! # Linear-in-degree height exponents for wide interpolation and its actual factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearHeightCurveBudget

open Polynomial BivariateDegrees BivariateHeight WidePlaneInterpolation

theorem interpolation_height_power (D N B : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (hB : B ≤ (D + 1) * N) : heightBound D B ≤ N ^ (128 * D) := by
  have hN : 2 ≤ N := hD.trans hDN
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 * N ≤ N ^ 2 := by simpa only [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left N hN
  have hDplus : D + 1 ≤ N ^ 2 := (show D + 1 ≤ 2 * N by omega).trans hN2
  have hB3 : B ≤ N ^ 3 := by
    calc
      _ ≤ (D + 1) * N := hB
      _ ≤ N ^ 2 * N := Nat.mul_le_mul_right N hDplus
      _ = _ := by ring
  have hcard : (2 * D + 1) ^ 2 ≤ N ^ 6 := by
    calc
      _ ≤ (3 * N) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 9 * N ^ 2 := by ring
      _ ≤ N ^ 4 * N ^ 2 := Nat.mul_le_mul_right _
        ((by decide : 9 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4))
      _ = _ := by ring
  have hthree : 3 ≤ N ^ 2 := (by decide : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hN 2)
  have hcoef : 3 * (2 * D + 1) ^ 2 ≤ N ^ 8 := by
    calc
      _ ≤ N ^ 2 * N ^ 6 := Nat.mul_le_mul hthree hcard
      _ = _ := by ring
  have hp : B ^ (4 * D) ≤ N ^ (12 * D) := by
    calc
      _ ≤ (N ^ 3) ^ (4 * D) := Nat.pow_le_pow_left hB3 _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hone : 1 ≤ N ^ (12 * D) := Nat.one_le_pow _ _ hN1
  have hsum : B ^ (4 * D) + 1 ≤ N ^ (12 * D + 1) := by
    calc
      _ ≤ 2 * N ^ (12 * D) := by omega
      _ ≤ N ^ (12 * D) * N := by nlinarith only [Nat.mul_le_mul_right (N ^ (12 * D)) hN]
      _ = _ := (pow_succ _ _).symm
  have hbase : 3 * (2 * D + 1) ^ 2 * (B ^ (4 * D) + 1) ≤ N ^ (12 * D + 9) := by
    calc
      _ ≤ N ^ 8 * N ^ (12 * D + 1) := Nat.mul_le_mul hcoef hsum
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ (N ^ (12 * D + 9)) ^ 7 := Nat.pow_le_pow_left hbase _
    _ = N ^ ((12 * D + 9) * 7) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem factor_height_power (D N B : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (hB : B ≤ (D + 1) * N) (Q C : ℤ[X][X]) (hQ : Q ≠ 0) (hCQ : C ∣ Q)
    (hdegree : PlaneCurvePointCount.degree Q ≤ 4 * D) (hheight : height Q ≤ heightBound D B) :
    height C ≤ N ^ (256 * D) := by
  have hN : 2 ≤ N := hD.trans hDN
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 * N ≤ N ^ 2 := by simpa only [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left N hN
  have hfour : 4 ≤ N ^ 2 := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hN 2)
  have hsize : 4 * D + 1 ≤ N ^ (2 * D) := by
    calc
      _ ≤ 4 * N ^ 2 := by nlinarith only [hDN, hN2, hN]
      _ ≤ N ^ 2 * N ^ 2 := Nat.mul_le_mul_right _ hfour
      _ = N ^ 4 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨U, hQU⟩ := hCQ
  have hU : U ≠ 0 := by intro hz; apply hQ; rw [hQU, hz, mul_zero]
  have hx : degreeX Q ≤ 4 * D := (BivariateCurveDegrees.degreeX_le_total Q).trans hdegree
  have hy : degreeY Q ≤ 4 * D := (BivariateCurveDegrees.degreeY_le_total Q).trans hdegree
  have hf := BivariateDivisionBounds.quotient_height Q U C hU (hQU.trans (mul_comm C U))
    (4 * D) (4 * D) (heightBound D B) hx hy hheight
  have hsqrt : Real.sqrt (((4 * D + 1) * (4 * D + 1) : ℕ) : ℝ) = ((4 * D + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_mul, ← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [show 4 * D + 4 * D = 8 * D by omega, hsqrt] at hf
  have hp : (2 : ℝ) ^ (8 * D) ≤ (N : ℝ) ^ (8 * D) :=
    pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hN) _
  have hs : ((4 * D + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 * D) := by exact_mod_cast hsize
  have hM : (heightBound D B : ℝ) ≤ (N : ℝ) ^ (128 * D) := by
    exact_mod_cast interpolation_height_power D N B hD hDN hB
  have hprod : (2 : ℝ) ^ (8 * D) * ((4 * D + 1 : ℕ) : ℝ) * heightBound D B ≤
      (N : ℝ) ^ (256 * D) := by
    calc
      _ ≤ (N : ℝ) ^ (8 * D) * (N : ℝ) ^ (2 * D) * (N : ℝ) ^ (128 * D) := by gcongr
      _ = (N : ℝ) ^ (138 * D) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hN1) (by omega)
  exact_mod_cast hf.trans hprod

end PaperP1.LinearHeightCurveBudget
