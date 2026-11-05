module

public import PaperP1.Arithmetic.PNTPrimePowerUpper
public import Mathlib.Analysis.SumIntegralComparisons

/-! # Exact-endpoint integral control of reciprocal-logarithmic powers

The integer cutoff is not enlarged. This matters when a moving exponent is
later evaluated at a finely specified saddle endpoint.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalLogPowerIntegral

open Finset Set MeasureTheory

def powerLog (σ x : ℝ) : ℝ := x ^ (-σ) / Real.log x

theorem powerLog_nonneg (σ : ℝ) {x : ℝ} (hx : 2 ≤ x) : 0 ≤ powerLog σ x := by
  exact div_nonneg (Real.rpow_nonneg (by linarith only [hx]) _) (Real.log_nonneg (by linarith only [hx]))

theorem powerLog_antitone (σ : ℝ) (hσ : 0 ≤ σ) : AntitoneOn (powerLog σ) (Ici 2) := by
  intro x hx y hy hxy
  have hxp : 0 < x := by have hh : 2 ≤ x := hx; linarith only [hh]
  have hxl : 0 < Real.log x := Real.log_pos (by have hh : 2 ≤ x := hx; linarith only [hh])
  have hyl : 0 < Real.log y := Real.log_pos (by have hh : 2 ≤ y := hy; linarith only [hh])
  have hp := Real.rpow_le_rpow_of_nonpos hxp hxy (neg_nonpos.mpr hσ)
  exact (div_le_div_of_nonneg_right hp hyl.le).trans
    (div_le_div_of_nonneg_left (Real.rpow_nonneg hxp.le _) hxl (Real.log_le_log hxp hxy))

theorem powerLog_continuous (σ : ℝ) : ContinuousOn (powerLog σ) (Ici 2) := by
  apply (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (by
    have hh : 2 ≤ x := hx
    linarith only [hh] : x ≠ 0))).div
      (Real.continuousOn_log.mono (by intro x hx; have hh : 2 ≤ x := hx; simp only [mem_compl_iff, mem_singleton_iff]; linarith only [hh]))
  intro x hx
  exact (Real.log_pos (by have hh : 2 ≤ x := hx; linarith only [hh])).ne'

theorem powerLog_intervalIntegrable (σ a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (powerLog σ) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  exact (powerLog_continuous σ).mono (fun _ hx ↦ ha.trans hx.1)

theorem shifted_sum_upper (σ : ℝ) (hσ : 0 ≤ σ) (Y : ℕ) (hY : 2 ≤ Y) :
    (∑ i ∈ range Y, PNTPrimePowerUpper.weight σ (i + 1)) ≤
      2 * PNTPrimePowerUpper.weight σ 2 + ∫ x in (2 : ℝ)..Y, powerLog σ x := by
  have hsplit : (∑ i ∈ range Y, PNTPrimePowerUpper.weight σ (i + 1)) =
      2 * PNTPrimePowerUpper.weight σ 2 +
        ∑ i ∈ range (Y - 2), powerLog σ (2 + (i + 1 : ℕ)) := by
    conv_lhs => rw [show Y = 2 + (Y - 2) by omega, sum_range_add]
    have hhead : (∑ i ∈ range 2, PNTPrimePowerUpper.weight σ (i + 1)) =
        2 * PNTPrimePowerUpper.weight σ 2 := by
      norm_num [sum_range_succ, PNTPrimePowerUpper.weight, two_mul]
    rw [hhead]
    congr 1
    apply sum_congr rfl
    intro i _
    dsimp only [PNTPrimePowerUpper.weight, powerLog]
    rw [max_eq_right (by omega : 2 ≤ 2 + i + 1)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc]
  have hanti : AntitoneOn (powerLog σ) (Icc 2 (2 + ((Y - 2 : ℕ) : ℝ))) :=
    (powerLog_antitone σ hσ).mono (fun _ hx ↦ hx.1)
  have hint := hanti.sum_le_integral
  have hend : (2 : ℝ) + ((Y - 2 : ℕ) : ℝ) = (Y : ℝ) := by
    rw [Nat.cast_sub hY]
    norm_num
  rw [hend] at hint
  rw [hsplit]
  exact add_le_add le_rfl hint

theorem real_cutoff_sum_upper (σ : ℝ) (hσ : 0 ≤ σ) (R : ℝ) (hR : 2 ≤ R) :
    (∑ i ∈ range ⌊R⌋₊, PNTPrimePowerUpper.weight σ (i + 1)) ≤
      2 * PNTPrimePowerUpper.weight σ 2 + ∫ x in (2 : ℝ)..R, powerLog σ x := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hY : 2 ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR0).mpr (by exact_mod_cast hR)
  have hY2 : (2 : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hY
  have hi : (∫ x in (2 : ℝ)..⌊R⌋₊, powerLog σ x) ≤ ∫ x in (2 : ℝ)..R, powerLog σ x := by
    apply intervalIntegral.integral_mono_interval le_rfl hY2 (Nat.floor_le hR0)
    · exact (ae_restrict_mem measurableSet_Ioc).mono (fun x hx ↦ powerLog_nonneg σ hx.1.le)
    · exact powerLog_intervalIntegrable σ 2 R le_rfl hR
  exact (shifted_sum_upper σ hσ _ hY).trans (add_le_add le_rfl hi)

end PaperP1.ReciprocalLogPowerIntegral
