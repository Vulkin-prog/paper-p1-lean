module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Uniform quadratic-support power budgets for polynomial determinants -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ResultantPowerBudget

theorem linear_budget (B q b n : ℕ) (hB : 1 ≤ B) (hqB : q ≤ B) (hn : n ≤ b * q) :
    n ≤ (B + 1) ^ (b + 1) := by
  have hb : b ≤ (B + 1) ^ b :=
    (show b < 2 ^ b from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
  calc
    n ≤ b * q := hn
    _ ≤ (B + 1) ^ b * (B + 1) := Nat.mul_le_mul hb (hqB.trans (Nat.le_succ B))
    _ = _ := (pow_succ _ _).symm

theorem determinant_budget (B q a b c n d H : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hn : n ≤ b * q) (hd : d ≤ a * q) (hH : H ≤ (B + 1) ^ (c * q)) :
    n.factorial * (((n * d + 1) * H) ^ n) ≤
      (B + 1) ^ (b * (c + a + 2 * b + 4) * q ^ 2) := by
  have hB : 1 ≤ B := hq.trans hqB
  have hnp := linear_budget B q b n hB hqB hn
  have hdp := linear_budget B q a d hB hqB hd
  have hnd : n * d ≤ (B + 1) ^ (a + b + 2) := by
    calc
      _ ≤ (B + 1) ^ (b + 1) * (B + 1) ^ (a + 1) := Nat.mul_le_mul hnp hdp
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hp₁ : 1 ≤ (B + 1) ^ (a + b + 2) :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hnd₁ : n * d + 1 ≤ (B + 1) ^ (a + b + 3) := by
    calc
      _ ≤ (B + 1) ^ (a + b + 2) + (B + 1) ^ (a + b + 2) := Nat.add_le_add hnd hp₁
      _ = 2 * (B + 1) ^ (a + b + 2) := by ring
      _ ≤ (B + 1) * (B + 1) ^ (a + b + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [← pow_succ']
  have hentry : (n * d + 1) * H ≤ (B + 1) ^ (a + b + 3 + c * q) := by
    calc
      _ ≤ (B + 1) ^ (a + b + 3) * (B + 1) ^ (c * q) := Nat.mul_le_mul hnd₁ hH
      _ = _ := (pow_add _ _ _).symm
  have hfact : n.factorial ≤ (B + 1) ^ ((b + 1) * n) := by
    simpa only [← pow_mul] using (Nat.factorial_le_pow n).trans (Nat.pow_le_pow_left hnp n)
  have hlinear : a + 2 * b + 4 + c * q ≤ (c + a + 2 * b + 4) * q := by
    calc
      _ = (a + 2 * b + 4) * 1 + c * q := by ring
      _ ≤ (a + 2 * b + 4) * q + c * q := Nat.add_le_add_right (Nat.mul_le_mul_left _ hq) _
      _ = _ := by ring
  have hexp : (a + 2 * b + 4 + c * q) * n ≤ b * (c + a + 2 * b + 4) * q ^ 2 := by
    calc
      _ ≤ ((c + a + 2 * b + 4) * q) * (b * q) := Nat.mul_le_mul hlinear hn
      _ = _ := by ring
  calc
    _ ≤ (B + 1) ^ ((b + 1) * n) * ((B + 1) ^ (a + b + 3 + c * q)) ^ n :=
      Nat.mul_le_mul hfact (Nat.pow_le_pow_left hentry n)
    _ = (B + 1) ^ ((a + 2 * b + 4 + c * q) * n) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hexp

theorem common_curve_budget (B q n d H : ℕ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hn : n ≤ 48 * q) (hd : d ≤ 24 * q) (hH : H ≤ (B + 1) ^ (2472 * q)) :
    n.factorial * (((n * d + 1) * H) ^ n) ≤ (B + 1) ^ (124608 * q ^ 2) := by
  simpa only [show 48 * (2472 + 24 + 2 * 48 + 4) = 124608 by decide] using
    determinant_budget B q 24 48 2472 n d H hq hqB hn hd hH

end PaperP1.ResultantPowerBudget
