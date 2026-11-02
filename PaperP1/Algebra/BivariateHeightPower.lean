module

public import PaperP1.Algebra.PolynomialHeightArithmetic
public import Mathlib.Tactic.Linarith

/-! # Explicit absorption of the finite coefficient dimensions into height powers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateHeightPower

open Polynomial PaperP1.BivariateDegrees PaperP1.PolynomialHeightArithmetic

theorem linear_dimension (B q : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B) : 32 * q + 1 ≤ (B + 1) ^ 6 := by
  have hB : 1 ≤ B := hq.trans hqB
  have hB₂ : B ≤ B ^ 2 := by
    simpa only [mul_one, pow_two] using Nat.mul_le_mul_left B hB
  have h₂ : 4 ≤ (B + 1) ^ 2 := by nlinarith
  have h₃ : 3 * B + 1 ≤ (B + 1) ^ 2 := by nlinarith
  have h₄ : 12 * B + 4 ≤ (B + 1) ^ 4 := by
    calc
      _ = 4 * (3 * B + 1) := by ring
      _ ≤ (B + 1) ^ 2 * (B + 1) ^ 2 := Nat.mul_le_mul h₂ h₃
      _ = _ := by ring
  calc
    32 * q + 1 ≤ 4 * (12 * B + 4) := by omega
    _ ≤ (B + 1) ^ 2 * (B + 1) ^ 4 := Nat.mul_le_mul h₂ h₄
    _ = _ := by ring

theorem two_le_power (B q : ℕ) (hq : 1 ≤ q) (hB : 1 ≤ B) : 2 ≤ (B + 1) ^ q := by
  calc
    2 ≤ B + 1 := by omega
    _ = (B + 1) ^ 1 := by simp
    _ ≤ (B + 1) ^ q := Nat.pow_le_pow_right (by omega) hq

theorem mul_power (P Q : ℤ[X][X]) (B q cP cQ : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hx : degreeX P + degreeX Q ≤ 32 * q) (hy : degreeY P + degreeY Q ≤ 32 * q)
    (hP : BivariateHeight.height P ≤ (B + 1) ^ (cP * q))
    (hQ : BivariateHeight.height Q ≤ (B + 1) ^ (cQ * q)) :
    BivariateHeight.height (P * Q) ≤ (B + 1) ^ ((cP + cQ + 12) * q) := by
  have hdim := linear_dimension B q hq hqB
  have hx' : degreeX P + degreeX Q + 1 ≤ (B + 1) ^ 6 := (by omega : _ ≤ 32 * q + 1) |>.trans hdim
  have hy' : degreeY P + degreeY Q + 1 ≤ (B + 1) ^ 6 := (by omega : _ ≤ 32 * q + 1) |>.trans hdim
  have hd : (degreeX P + degreeX Q + 1) * (degreeY P + degreeY Q + 1) ≤ (B + 1) ^ (12 * q) := by
    calc
      _ ≤ (B + 1) ^ 6 * (B + 1) ^ 6 := Nat.mul_le_mul hx' hy'
      _ = (B + 1) ^ 12 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ _ := bivariate_height_mul P Q
    _ ≤ (B + 1) ^ (12 * q) * (B + 1) ^ (cP * q) * (B + 1) ^ (cQ * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul hd hP) hQ
    _ = _ := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem sum_power (B q c a b : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (ha : a ≤ (B + 1) ^ (c * q)) (hb : b ≤ (B + 1) ^ (c * q)) :
    a + b ≤ (B + 1) ^ ((c + 1) * q) := by
  have ht := two_le_power B q hq (hq.trans hqB)
  calc
    a + b ≤ (B + 1) ^ (c * q) + (B + 1) ^ (c * q) := Nat.add_le_add ha hb
    _ = 2 * (B + 1) ^ (c * q) := by ring
    _ ≤ (B + 1) ^ q * (B + 1) ^ (c * q) := Nat.mul_le_mul_right _ ht
    _ = _ := by
      rw [← pow_add]
      congr 1
      ring

theorem scalar_four (P : ℤ[X][X]) (B q c : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hP : BivariateHeight.height P ≤ (B + 1) ^ (c * q)) :
    BivariateHeight.height (4 * P) ≤ (B + 1) ^ ((c + 2) * q) := by
  have ht := two_le_power B q hq (hq.trans hqB)
  have hf : 4 ≤ (B + 1) ^ (2 * q) := by
    calc
      4 = 2 * 2 := rfl
      _ ≤ (B + 1) ^ q * (B + 1) ^ q := Nat.mul_le_mul ht ht
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ 4 * BivariateHeight.height P := bivariate_height_scalar 4 P
    _ ≤ (B + 1) ^ (2 * q) * (B + 1) ^ (c * q) := Nat.mul_le_mul hf hP
    _ = _ := by
      rw [← pow_add]
      congr 1
      ring

end PaperP1.BivariateHeightPower
