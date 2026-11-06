module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Fixed curve budgets and fixed height inflation are absorbed before all later point heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledFiniteCoverBudget

theorem exists_constant (L M B : ℕ) (A p q : ℝ) (hA : 0 < A) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H → ∀ v s t f : ℕ,
      v ≤ t → s ≤ B + f * M →
      (t : ℝ) ≤ A * ((L * H : ℕ) : ℝ) ^ q →
      (f : ℝ) ≤ A * ((L * H : ℕ) : ℝ) ^ p →
      (v : ℝ) ≤ C * (H : ℝ) ^ q ∧ (s : ℝ) ≤ C * (H : ℝ) ^ p := by
  let a := A * (L : ℝ) ^ q
  let b := (M : ℝ) * A * (L : ℝ) ^ p
  let C := 1 + (B : ℝ) + b + a
  have ha : 0 ≤ a := mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg L) q)
  have hb : 0 ≤ b := mul_nonneg (mul_nonneg (Nat.cast_nonneg M) hA.le) (Real.rpow_nonneg (Nat.cast_nonneg L) p)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro H hH v s t f hvt hs ht hf
  have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : 1 ≤ (H : ℝ) ^ p := Real.one_le_rpow hHreal hp
  have ht' : (t : ℝ) ≤ a * (H : ℝ) ^ q := by
    simpa only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg L) (Nat.cast_nonneg H), a, mul_assoc] using ht
  have hf' : (f : ℝ) * M ≤ b * (H : ℝ) ^ p := by
    have hh := mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg L) (Nat.cast_nonneg H)] at hh
    convert hh using 1
    dsimp [b]
    ring
  have hs' : (s : ℝ) ≤ (B : ℝ) + (f : ℝ) * M := by exact_mod_cast hs
  constructor
  · have hv' : (v : ℝ) ≤ t := by exact_mod_cast hvt
    exact (hv'.trans ht').trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (Nat.cast_nonneg H) q))
  · calc
      (s : ℝ) ≤ (B : ℝ) + b * (H : ℝ) ^ p := by linarith [hs', hf']
      _ ≤ (B : ℝ) * (H : ℝ) ^ p + b * (H : ℝ) ^ p := by
        gcongr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hHp (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
      _ = ((B : ℝ) + b) * (H : ℝ) ^ p := by ring
      _ ≤ C * (H : ℝ) ^ p := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (Real.rpow_nonneg (Nat.cast_nonneg H) p)

end PaperP1.ScaledFiniteCoverBudget
