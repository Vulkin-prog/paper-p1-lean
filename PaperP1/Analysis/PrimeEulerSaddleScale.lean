module

public import PaperP1.Arithmetic.PrimeHarmonicUpper
public import PaperP1.Analysis.HardSaddleGrowth

/-! # A finite Euler exponent bound at a moving hard-saddle cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeEulerSaddleScale

open PrimeHarmonicUpper

theorem exponent_bound (C H V : ℝ) (hC : 0 ≤ C) (hH : 4 ≤ H)
    (hlog : 1 ≤ Real.log H) (hV : 1 ≤ V) (hVH : V ≤ H) (hroot : Real.sqrt H ≤ V)
    (hsmall : 24 * C * Real.log H ≤ H ^ (1 / 4 : ℝ)) (Y : ℕ) (hY : 2 ≤ Y)
    (hcut : (Y : ℝ) ≤ Real.exp V) :
    C * (Y : ℝ) ^ (Real.log H / (4 * V)) * (1 + Real.log (Real.log ((Y : ℝ) + 2))) ≤ V / 8 := by
  have hHp : 0 < H := by linarith only [hH]
  have hVp : 0 < V := by linarith only [hV]
  have hlogp : 0 < Real.log H := by linarith only [hlog]
  have hYpow : (Y : ℝ) ^ (Real.log H / (4 * V)) ≤ H ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (Real.exp V) ^ (Real.log H / (4 * V)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg Y) hcut (by positivity)
      _ = Real.exp (Real.log H / 4) := by
        rw [← Real.exp_mul]
        congr 1
        field_simp
      _ = _ := by rw [Real.rpow_def_of_pos hHp]; congr 1; ring
  have heV : 2 ≤ Real.exp V := by have hh := Real.add_one_le_exp V; linarith only [hh, hV]
  have hYplus : (Y : ℝ) + 2 ≤ 2 * Real.exp V := by linarith only [hcut, heV]
  have hlog2 : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hYpluspos : 0 < (Y : ℝ) + 2 := by positivity
  have hlogY : Real.log ((Y : ℝ) + 2) ≤ 2 * H := by
    calc
      _ ≤ Real.log (2 * Real.exp V) := Real.log_le_log hYpluspos hYplus
      _ = Real.log 2 + V := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
      _ ≤ _ := by linarith only [hlog2, hV, hVH]
  have hlogYpos : 0 < Real.log ((Y : ℝ) + 2) := Real.log_pos (by
    have hy : (2 : ℝ) ≤ Y := by exact_mod_cast hY
    linarith only [hy])
  have houter : Real.log (Real.log ((Y : ℝ) + 2)) ≤ 2 * Real.log H := by
    calc
      _ ≤ Real.log (2 * H) := Real.log_le_log hlogYpos hlogY
      _ = Real.log 2 + Real.log H := by rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHp.ne']
      _ ≤ _ := by linarith only [hlog2, hlog]
  have hquarter : (H ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt H := by
    rw [← Real.rpow_mul_natCast hHp.le]
    norm_num
    exact (Real.sqrt_eq_rpow H).symm
  have hmain : C * H ^ (1 / 4 : ℝ) * (3 * Real.log H) ≤ Real.sqrt H / 8 := by
    have hh := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hHp.le (1 / 4))
    nlinarith only [hh, hquarter]
  calc
    _ ≤ C * (Y : ℝ) ^ (Real.log H / (4 * V)) * (3 * Real.log H) :=
      mul_le_mul_of_nonneg_left (by linarith only [houter, hlog]) (by positivity)
    _ ≤ C * H ^ (1 / 4 : ℝ) * (3 * Real.log H) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYpow hC) (by positivity)
    _ ≤ Real.sqrt H / 8 := hmain
    _ ≤ V / 8 := div_le_div_of_nonneg_right hroot (by norm_num)

end PaperP1.PrimeEulerSaddleScale
