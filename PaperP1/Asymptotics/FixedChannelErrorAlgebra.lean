module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # The three finite channel errors are bounded by a square-logarithmic baseline -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelErrorAlgebra

theorem error_scale {N B P U X R Kp K₀ : ℝ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hU : 0 ≤ U) (hX : 0 ≤ X) (hR : 0 ≤ R) (hKp : 0 ≤ Kp) (hK₀ : 0 ≤ K₀)
    (hPbound : P ≤ Kp * N ^ (-2 : ℝ))
    (hUbound : U ≤ B ^ 2 * K₀ * N ^ (1 / 3 : ℝ))
    (hXbound : X ≤ N ^ (7 / 12 : ℝ))
    (hRbound : R ≤ K₀ * N ^ (1 / 3 : ℝ))
    (hBbound : B ≤ N ^ (2 / 3 : ℝ)) :
    P * (6 * B * U + 2 * B ^ 2 * N + 2 * X * R) ≤
      Kp * (8 * K₀ + 2) * B ^ 2 * N ^ (-1 : ℝ) := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hb : 0 ≤ B := le_trans zero_le_one hB
  have hBsq : 1 ≤ B ^ 2 := by nlinarith
  have hendpoint : B * N ^ (-2 : ℝ) * N ^ (1 / 3 : ℝ) ≤ N ^ (-1 : ℝ) := by
    calc
      _ ≤ N ^ (2 / 3 : ℝ) * N ^ (-2 : ℝ) * N ^ (1 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBbound (Real.rpow_nonneg hn.le _))
          (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; norm_num
  have hbaseline : N ^ (-2 : ℝ) * N = N ^ (-1 : ℝ) := by
    calc
      _ = N ^ (-2 : ℝ) * N ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn]; norm_num
  have hbad : N ^ (-2 : ℝ) * N ^ (7 / 12 : ℝ) * N ^ (1 / 3 : ℝ) ≤ N ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  have h₁ : P * B * U ≤ Kp * K₀ * B ^ 2 * N ^ (-1 : ℝ) := by
    calc
      _ ≤ (Kp * N ^ (-2 : ℝ)) * B * (B ^ 2 * K₀ * N ^ (1 / 3 : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hPbound hb) hUbound hU
          (mul_nonneg (mul_nonneg hKp (Real.rpow_nonneg hn.le _)) hb)
      _ = (Kp * K₀ * B ^ 2) * (B * N ^ (-2 : ℝ) * N ^ (1 / 3 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hendpoint (by positivity)
  have h₂ : P * B ^ 2 * N ≤ Kp * B ^ 2 * N ^ (-1 : ℝ) := by
    calc
      _ ≤ (Kp * N ^ (-2 : ℝ)) * B ^ 2 * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPbound (sq_nonneg _)) hn.le
      _ = Kp * B ^ 2 * (N ^ (-2 : ℝ) * N) := by ring
      _ = _ := by rw [hbaseline]
  have h₃ : P * X * R ≤ Kp * K₀ * B ^ 2 * N ^ (-1 : ℝ) := by
    calc
      _ ≤ (Kp * N ^ (-2 : ℝ)) * N ^ (7 / 12 : ℝ) * (K₀ * N ^ (1 / 3 : ℝ)) :=
        mul_le_mul (mul_le_mul hPbound hXbound hX (mul_nonneg hKp (Real.rpow_nonneg hn.le _)))
          hRbound hR (by positivity)
      _ = (Kp * K₀) * (N ^ (-2 : ℝ) * N ^ (7 / 12 : ℝ) * N ^ (1 / 3 : ℝ)) := by ring
      _ ≤ (Kp * K₀) * N ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left hbad (mul_nonneg hKp hK₀)
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hBsq (mul_nonneg hKp hK₀)
        have ht := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hn.le (-1 : ℝ))
        simpa only [mul_one] using ht
  nlinarith only [h₁, h₂, h₃]

end PaperP1.FixedChannelErrorAlgebra
