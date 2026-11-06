module

public import PaperP1.Analysis.PrimeSelbergCoefficients
public import PaperP1.Analysis.SeparatedGaussianBudget


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PowerSelbergLevel
open Finset Filter PaperP1
open scoped Classical

def level (η A : ℝ) : ℕ := ⌊A^η⌋₊

theorem level_pos (η A : ℝ) (hη : 0 ≤ η) (hA : 1 ≤ A) : 1 ≤ level η A := by
  apply (Nat.le_floor_iff (Real.rpow_nonneg (by linarith only [hA]) η)).mpr
  simpa only [Nat.cast_one] using Real.one_le_rpow hA hη

theorem level_le (η A : ℝ) (hA : 0 ≤ A) : (level η A : ℝ) ≤ A^η :=
  Nat.floor_le (Real.rpow_nonneg hA η)

theorem level_square_bound (η A : ℝ) (hη : η ≤ 1/4) (hA : 1 ≤ A) : (level η A : ℝ)^2 ≤ Real.sqrt A := by
  have hAP : 0 < A := by linarith only [hA]
  calc
    _ ≤ (A^η)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (level_le η A hAP.le) 2
    _ = A^(2*η) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hAP.le]
      congr 1
      ring
    _ ≤ A^(1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by linarith only [hη])
    _ = _ := Real.sqrt_eq_rpow A |>.symm

theorem level_lt_scale (η A : ℝ) (hη : η < 1) (hA : 1 < A) : (level η A : ℝ) < A := by
  have hh := Real.rpow_lt_rpow_of_exponent_lt hA hη
  rw [Real.rpow_one] at hh
  exact (level_le η A (by linarith only [hA])).trans_lt hh

theorem denominator_lower (η A : ℝ) (hA : 0 < A) :
    η*Real.log A/2 ≤ PrimeSelbergCoefficients.denominator (level η A) := by
  have hTop : A^η ≤ ((level η A+1 : ℕ) : ℝ) := by
    simpa only [level,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (A^η)).le
  have hLog := Real.log_le_log (Real.rpow_pos_of_pos hA η) hTop
  rw [Real.log_rpow hA] at hLog
  linarith only [hLog,PrimeSelbergCoefficients.denominator_log_lower (level η A)]

theorem main_bound (η A : ℝ) (hη : 0 < η) (hA : 1 < A) :
    A*Real.sqrt Real.pi/PrimeSelbergCoefficients.denominator (level η A) ≤
      (2*Real.sqrt Real.pi/η)*A/Real.log A := by
  have hAP : 0 < A := by linarith only [hA]
  have hLog : 0 < Real.log A := Real.log_pos hA
  have hDen : 0 < η*Real.log A/2 := by positivity
  calc
    _ ≤ A*Real.sqrt Real.pi/(η*Real.log A/2) :=
      div_le_div_of_nonneg_left (by positivity) hDen (denominator_lower η A hAP)
    _ = _ := by field_simp [hη.ne',hLog.ne']

theorem level_fourth_bound (η A : ℝ) (hA : 0 < A) : (level η A : ℝ)^4 ≤ A^(4*η) := by
  calc
    _ ≤ (A^η)^4 := pow_le_pow_left₀ (Nat.cast_nonneg _) (level_le η A hA.le) 4
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
      congr 1
      ring
end PaperP1.PowerSelbergLevel
