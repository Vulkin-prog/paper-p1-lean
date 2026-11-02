module

public import PaperP1.Analysis.ShortBasisParameters
public import PaperP1.Arithmetic.LogarithmicPrimeCount

/-! # The actual final small-prime cost at the real cutoff B^a -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallPrimeShortBasisBudget

open PaperP1.LogarithmicPrimeCount

def constant (a : ℝ) : ℝ := 32 / a

theorem constant_pos (a : ℝ) (ha : 0 < a) : 0 < constant a := by
  exact div_pos (by norm_num) ha

theorem power_ge_eight (B a : ℝ) (hB : 1 < B) (haB : 4 ≤ a * Real.log B) : 8 ≤ B ^ a := by
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  apply (Real.le_rpow_iff_log_le (by norm_num) (by linarith : 0 < B)).mpr
  linarith

theorem log_floor_power_lower (B a : ℝ) (hB : 1 < B) (haB : 4 ≤ a * Real.log B) :
    a * Real.log B / 2 ≤ Real.log (⌊B ^ a⌋₊ : ℝ) := by
  have hBp : 0 < B := by linarith
  have hT := power_ge_eight B a hB haB
  have hTpos : 0 < B ^ a := Real.rpow_pos_of_pos hBp a
  have hfloor := Nat.lt_floor_add_one (B ^ a)
  have hhalf : B ^ a / 2 ≤ (⌊B ^ a⌋₊ : ℝ) := by linarith
  have hlog := Real.log_le_log (div_pos hTpos (by norm_num)) hhalf
  rw [Real.log_div hTpos.ne' (by norm_num), Real.log_rpow hBp a] at hlog
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  linarith

theorem constraint_cost (B a : ℝ) (hB : 1 < B) (ha : 0 < a)
    (haB : 4 ≤ a * Real.log B) :
    (primeCount ⌊B ^ a⌋₊ : ℝ) + 3 ≤ constant a * B ^ a / Real.log B := by
  have hBp : 0 < B := by linarith
  have hs : 0 < Real.log B := Real.log_pos hB
  have hT := power_ge_eight B a hB haB
  have hTpos : 0 < B ^ a := Real.rpow_pos_of_pos hBp a
  have hz : 4 ≤ ⌊B ^ a⌋₊ := by
    apply Nat.le_floor
    norm_num
    linarith
  have hlog := log_floor_power_lower B a hB haB
  have hcount := LogarithmicPrimeCount.log_mul_primeCount_le hz
  have hfloor := Nat.floor_le hTpos.le
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hπ : (0 : ℝ) ≤ primeCount ⌊B ^ a⌋₊ := Nat.cast_nonneg _
  have hz₀ : (0 : ℝ) ≤ ⌊B ^ a⌋₊ := Nat.cast_nonneg _
  have hcount' : (primeCount ⌊B ^ a⌋₊ : ℝ) * Real.log (⌊B ^ a⌋₊ : ℝ) ≤ 14 * B ^ a := by
    have hmul := mul_le_mul_of_nonneg_right htwo hz₀
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlog hπ
  have hprime : (primeCount ⌊B ^ a⌋₊ : ℝ) * a * Real.log B ≤ 28 * B ^ a := by nlinarith
  have hlinear := (le_div_iff₀ ha).mp (Real.log_le_rpow_div hBp.le ha)
  unfold constant
  apply (le_div_iff₀ hs).mpr
  rw [show 32 / a * B ^ a = 32 * B ^ a / a by ring]
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem constraint_cost_le_large_scale (B a : ℝ) (hB : 1 < B) (ha : 0 < a)
    (ha₁ : a ≤ 1) (hs : 64 ≤ Real.log B) (haB : 4 ≤ a * Real.log B) :
    (primeCount ⌊B ^ a⌋₊ : ℝ) + 2 ≤ constant a * B / Real.sqrt (Real.log B) := by
  have hBp : 0 < B := by linarith
  have hs₀ : 0 < Real.log B := Real.log_pos hB
  have hr : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.mpr hs₀
  have hrle : Real.sqrt (Real.log B) ≤ Real.log B := by
    have hsq := Real.sq_sqrt hs₀.le
    have hr₀ := Real.sqrt_nonneg (Real.log B)
    nlinarith
  have hpower : B ^ a ≤ B := Real.rpow_le_self_of_one_le hB.le ha₁
  have hc := constraint_cost B a hB ha haB
  have hconst := (constant_pos a ha).le
  calc
    (primeCount ⌊B ^ a⌋₊ : ℝ) + 2 ≤ constant a * B ^ a / Real.log B := by linarith
    _ ≤ constant a * B / Real.log B := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hconst) hs₀.le
    _ ≤ constant a * B / Real.sqrt (Real.log B) :=
      div_le_div_of_nonneg_left (mul_nonneg hconst hBp.le) hr hrle

end PaperP1.SmallPrimeShortBasisBudget
