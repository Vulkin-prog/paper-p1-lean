module

public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity

/-! # Quantitative first and second order finite-product perturbations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BanachPowerPerturbation

variable {A : Type*} [NormedCommRing A] [NormOneClass A]

theorem norm_pow_sub_le (x y : A) (M : ℝ) (hM : 1 ≤ M)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * M ^ n * ‖x - y‖ := by
  have hM0 : 0 ≤ M := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have hid : x ^ (n + 1) - y ^ (n + 1) =
        x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    have hpow : ‖y ^ n‖ ≤ M ^ n := (norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg y) hy n)
    calc
      _ ≤ ‖x‖ * ‖x ^ n - y ^ n‖ + ‖x - y‖ * ‖y ^ n‖ := by
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * ((n : ℝ) * M ^ n * ‖x - y‖) + ‖x - y‖ * M ^ n :=
        add_le_add (mul_le_mul hx ih (norm_nonneg _) hM0)
          (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ M ^ n * ‖x - y‖)
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith only [h]

omit [NormOneClass A] in
theorem second_order_identity (x y : A) (n : ℕ) :
    x ^ (n + 2) - y ^ (n + 2) - (n + 2) • ((x - y) * y ^ (n + 1)) =
      x * (x ^ (n + 1) - y ^ (n + 1) - (n + 1) • ((x - y) * y ^ n)) +
        (n + 1) • ((x - y) ^ 2 * y ^ n) := by
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
  ring

theorem norm_second_order_le (x y : A) (M : ℝ) (hM : 1 ≤ M)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1) - (n + 1) • ((x - y) * y ^ n)‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) * ‖x - y‖ ^ 2 := by
  have hM0 : 0 ≤ M := by linarith
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    have hpow : ‖y ^ n‖ ≤ M ^ n := (norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg y) hy n)
    have hcross : ‖(n + 1) • ((x - y) ^ 2 * y ^ n)‖ ≤
        ((n + 1 : ℕ) : ℝ) * (‖x - y‖ ^ 2 * M ^ n) := by
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) * ‖(x - y) ^ 2 * y ^ n‖ := norm_nsmul_le
        _ ≤ _ := by
          gcongr
          exact (norm_mul_le _ _).trans
            (mul_le_mul (norm_pow_le (x - y) 2) hpow (norm_nonneg _) (by positivity))
    have hMstep : M ^ n ≤ M ^ (n + 2) := by
      exact pow_le_pow_right₀ hM (by omega)
    calc
      _ ≤ ‖x‖ * ‖x ^ (n + 1) - y ^ (n + 1) - (n + 1) • ((x - y) * y ^ n)‖ +
          ‖(n + 1) • ((x - y) ^ 2 * y ^ n)‖ := by
        rw [show n + 1 + 1 = n + 2 by omega, second_order_identity]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ M * (((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) * ‖x - y‖ ^ 2) +
          ((n + 1 : ℕ) : ℝ) * (‖x - y‖ ^ 2 * M ^ n) :=
        add_le_add (mul_le_mul hx ih (norm_nonneg _) hM0) hcross
      _ ≤ M * (((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) * ‖x - y‖ ^ 2) +
          ((n + 1 : ℕ) : ℝ) * (‖x - y‖ ^ 2 * M ^ (n + 2)) := by gcongr
      _ ≤ _ := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        have hp : 0 ≤ M ^ n * M * M * ‖x - y‖ ^ 2 := by positivity
        nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity) hp]

omit [NormOneClass A] in
theorem corrected_power_identity (x y q : A) (n : ℕ) :
    x ^ (n + 1) - y ^ (n + 1) + (n + 1) • (q * y ^ (n + 1)) =
      (x ^ (n + 1) - y ^ (n + 1) - (n + 1) • ((x - y) * y ^ n)) +
        (n + 1) • ((x - y + q) * y ^ n) +
        (n + 1) • (q * (y - 1) * y ^ n) := by
  simp only [nsmul_eq_mul, pow_succ]
  ring

theorem norm_corrected_power_le (x y q : A) (M : ℝ) (hM : 1 ≤ M)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1) + (n + 1) • (q * y ^ (n + 1))‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) * ‖x - y‖ ^ 2 +
        ((n + 1 : ℕ) : ℝ) * (‖x - y + q‖ + ‖q‖ * ‖y - 1‖) * M ^ n := by
  have hpow : ‖y ^ n‖ ≤ M ^ n :=
    (norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg y) hy n)
  have hfirst : ‖(n + 1) • ((x - y + q) * y ^ n)‖ ≤
      ((n + 1 : ℕ) : ℝ) * (‖x - y + q‖ * M ^ n) := by
    exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_left
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)))
      (Nat.cast_nonneg _))
  have hsecond : ‖(n + 1) • (q * (y - 1) * y ^ n)‖ ≤
      ((n + 1 : ℕ) : ℝ) * (‖q‖ * ‖y - 1‖ * M ^ n) := by
    apply norm_nsmul_le.trans
    gcongr
    exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_mul_le _ _) hpow (norm_nonneg _) (by positivity))
  calc
    _ ≤ (‖x ^ (n + 1) - y ^ (n + 1) - (n + 1) • ((x - y) * y ^ n)‖ +
        ‖(n + 1) • ((x - y + q) * y ^ n)‖) +
        ‖(n + 1) • (q * (y - 1) * y ^ n)‖ := by
      rw [corrected_power_identity]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      have h := add_le_add (add_le_add (norm_second_order_le x y M hM hx hy n) hfirst) hsecond
      convert h using 1; ring

end PaperP1.BanachPowerPerturbation
