module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The fourth Charlier polynomial and an explicit uniform polynomial envelope -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourthCharlierPolynomial

def value (μ : ℝ) (k : ℕ) : ℝ :=
  (k.descFactorial 4 : ℝ) - 4 * μ * (k.descFactorial 3 : ℝ) +
    6 * μ ^ 2 * (k.descFactorial 2 : ℝ) - 4 * μ ^ 3 * k + μ ^ 4

theorem factorial_envelope (k j : ℕ) (hj : j ≤ 4) :
    (k.descFactorial j : ℝ) ≤ (1 + (k : ℝ)) ^ 4 := by
  have hsmall : (k.descFactorial j : ℝ) ≤ (k : ℝ) ^ j := by
    exact_mod_cast Nat.descFactorial_le_pow k j
  exact hsmall.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (k : ℝ) ≤ 1 + k) j).trans
    (pow_le_pow_right₀ (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k] : (1 : ℝ) ≤ 1 + k) hj))

theorem envelope {μ M : ℝ} (hμ : 0 ≤ μ) (hμM : μ ≤ M) (k : ℕ) :
    |value μ k| ≤ (1 + M) ^ 4 * (1 + (k : ℝ)) ^ 4 := by
  have hM : 0 ≤ M := hμ.trans hμM
  have h4 := factorial_envelope k 4 le_rfl
  have h3 := factorial_envelope k 3 (by norm_num)
  have h2 := factorial_envelope k 2 (by norm_num)
  have h1 : (k : ℝ) ≤ (1 + (k : ℝ)) ^ 4 := by
    simpa only [Nat.descFactorial_one] using factorial_envelope k 1 (by norm_num)
  have h0 : (1 : ℝ) ≤ (1 + (k : ℝ)) ^ 4 := one_le_pow₀ (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k])
  have hp2 := pow_le_pow_left₀ hμ hμM 2
  have hp3 := pow_le_pow_left₀ hμ hμM 3
  have hp4 := pow_le_pow_left₀ hμ hμM 4
  have ha := abs_add_le
    ((k.descFactorial 4 : ℝ) - 4 * μ * (k.descFactorial 3 : ℝ) +
      6 * μ ^ 2 * (k.descFactorial 2 : ℝ) - 4 * μ ^ 3 * k) (μ ^ 4)
  have hb := abs_sub
    ((k.descFactorial 4 : ℝ) - 4 * μ * (k.descFactorial 3 : ℝ) +
      6 * μ ^ 2 * (k.descFactorial 2 : ℝ)) (4 * μ ^ 3 * k)
  have hc := abs_add_le ((k.descFactorial 4 : ℝ) - 4 * μ * (k.descFactorial 3 : ℝ))
    (6 * μ ^ 2 * (k.descFactorial 2 : ℝ))
  have hd := abs_sub (k.descFactorial 4 : ℝ) (4 * μ * (k.descFactorial 3 : ℝ))
  rw [abs_of_nonneg (by positivity : 0 ≤ μ ^ 4)] at ha
  rw [abs_of_nonneg (by positivity : 0 ≤ 4 * μ ^ 3 * k)] at hb
  rw [abs_of_nonneg (by positivity : 0 ≤ 6 * μ ^ 2 * (k.descFactorial 2 : ℝ))] at hc
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (k.descFactorial 4 : ℝ) from Nat.cast_nonneg _), abs_of_nonneg (by positivity : 0 ≤ 4 * μ * (k.descFactorial 3 : ℝ))] at hd
  have hterm3 := mul_le_mul hμM h3 (Nat.cast_nonneg _) hM
  have hterm2 := mul_le_mul hp2 h2 (Nat.cast_nonneg _) (sq_nonneg M)
  have hterm1 := mul_le_mul hp3 h1 (Nat.cast_nonneg _) (pow_nonneg hM 3)
  have hterm0 := mul_le_mul_of_nonneg_left h0 (pow_nonneg hM 4)
  dsimp only [value]
  nlinarith only [ha, hb, hc, hd, h4, hterm3, hterm2, hterm1, hp4, hterm0]

end PaperP1.FourthCharlierPolynomial
