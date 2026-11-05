module

public import PaperP1.Analysis.ReciprocalLogPowerIntegral
public import PaperP1.Analysis.ExponentialIntegral

/-! # Exact exponential-integral primitive for a moving reciprocal-logarithmic power

The standard Ei normalization, including its value at one, is retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExponentialIntegralPowerLog

open Set MeasureTheory ReciprocalLogPowerIntegral ExponentialIntegral

theorem hasDerivAt_primitive (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ exponentialIntegral (δ * Real.log t)) (powerLog (1 - δ) x) x := by
  have hxp : 0 < x := by linarith only [hx]
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hi := (Real.hasDerivAt_log hxp.ne').const_mul δ
  have hh := (hasDerivAt_exponentialIntegral (mul_pos hδ hlog)).comp x hi
  apply hh.congr_deriv
  rw [powerLog, Real.rpow_def_of_pos hxp,
    show Real.log x * -(1 - δ) = δ * Real.log x - Real.log x by ring,
    Real.exp_sub, Real.exp_log hxp]
  field_simp

theorem integral_identity (δ a b : ℝ) (hδ : 0 < δ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, powerLog (1 - δ) x) =
      exponentialIntegral (δ * Real.log b) - exponentialIntegral (δ * Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_primitive δ hδ x (by have hh := ha.trans hx.1; linarith only [hh])
  · exact powerLog_intervalIntegrable (1 - δ) a b ha hab

theorem lower_small (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    exponentialIntegralAnchor + Real.exp 1 * Real.log u ≤ exponentialIntegral u := by
  have hcont : ContinuousOn (fun t : ℝ ↦ Real.exp 1 / t) (uIcc u 1) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [uIcc_of_le hu1] at ht
    exact (hu.trans_le ht.1).ne'
  have hcomp := intervalIntegral.integral_mono_on hu1 (intervalIntegrable_integrand hu).symm
    hcont.intervalIntegrable (by
      intro t ht
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ht.2) (hu.le.trans ht.1))
  have hint : (∫ t in u..1, Real.exp 1 / t) = Real.exp 1 * Real.log (1 / u) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hu (by norm_num : (0 : ℝ) < 1)]
    simp only [one_div, one_mul]
  rw [hint, one_div, Real.log_inv] at hcomp
  have hid : exponentialIntegral u = exponentialIntegralAnchor - ∫ t in u..1, Real.exp t / t := by
    rw [exponentialIntegral, intervalIntegral.integral_symm]
    ring
  linarith only [hcomp, hid]

def smallEndpointConstant : ℝ :=
  2 / Real.log 2 + |exponentialIntegralAnchor| + Real.exp 1 * |Real.log (Real.log 2)|

theorem smallEndpointConstant_pos : 0 < smallEndpointConstant := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  dsimp only [smallEndpointConstant]
  positivity

theorem integer_sum_upper (δ R : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hR : 2 ≤ R) :
    (∑ i ∈ Finset.range ⌊R⌋₊, PNTPrimePowerUpper.weight (1 - δ) (i + 1)) ≤
      exponentialIntegral (δ * Real.log R) + Real.exp 1 * Real.log (1 / δ) + smallEndpointConstant := by
  have hσ : 0 ≤ 1 - δ := by linarith only [hδhalf]
  have hbase := real_cutoff_sum_upper (1 - δ) hσ R hR
  rw [integral_identity δ 2 R hδ le_rfl hR] at hbase
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hu1 : δ * Real.log 2 ≤ 1 := by
    have hh := mul_le_mul hδhalf hl2le hl2.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [hh]
  have hEi := lower_small (δ * Real.log 2) (mul_pos hδ hl2) hu1
  rw [Real.log_mul hδ.ne' hl2.ne'] at hEi
  have hhead : 2 * PNTPrimePowerUpper.weight (1 - δ) 2 ≤ 2 / Real.log 2 := by
    have hh := PNTPrimePowerUpper.weight_one_le (1 - δ) hσ
    change (2 : ℝ) ^ (-(1 - δ)) / Real.log 2 ≤ 1 / Real.log 2 at hh
    change 2 * ((2 : ℝ) ^ (-(1 - δ)) / Real.log 2) ≤ 2 / Real.log 2
    calc
      _ ≤ 2 * (1 / Real.log 2) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hanchor := neg_le_abs exponentialIntegralAnchor
  have hlog := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log (Real.log 2))) (Real.exp_nonneg 1)
  have hinv : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  rw [hinv]
  dsimp only [smallEndpointConstant]
  nlinarith only [hbase, hEi, hhead, hanchor, hlog]

theorem uniform_euler_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ R : ℝ, 0 < δ → δ ≤ 1 / 2 → 2 ≤ R →
      SmallKernelCount.eulerProduct ⌊R⌋₊ (1 - δ) ≤
        Real.exp (C + (1 + η) * exponentialIntegral (δ * Real.log R) +
          (1 + η) * Real.exp 1 * Real.log (1 / δ)) := by
  obtain ⟨C₀, hC₀, he⟩ := PNTPrimePowerUpper.uniform_euler_upper η hη
  let C := C₀ + (1 + η) * smallEndpointConstant
  have hC : 0 < C := by have := smallEndpointConstant_pos; dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ R hδ hδhalf hR
  have hσ : 0 ≤ 1 - δ := by linarith only [hδhalf]
  have hh := he (1 - δ) hσ ⌊R⌋₊
  have hs := mul_le_mul_of_nonneg_left (integer_sum_upper δ R hδ hδhalf hR)
    (by linarith only [hη] : 0 ≤ 1 + η)
  have hbound : C₀ + (1 + η) * (∑ i ∈ Finset.range ⌊R⌋₊, PNTPrimePowerUpper.weight (1 - δ) (i + 1)) ≤
      C + (1 + η) * exponentialIntegral (δ * Real.log R) +
        (1 + η) * Real.exp 1 * Real.log (1 / δ) := by
    dsimp only [C]
    nlinarith only [hs]
  exact hh.trans (Real.exp_le_exp.mpr hbound)

theorem uniform_pivot_count (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, ∀ δ R : ℝ, 0 < δ → δ ≤ 1 / 2 → 2 ≤ R →
      ((OddPrimePivot.pivotValues X ⌊R⌋₊).card : ℝ) ≤ (X : ℝ) ^ (1 - δ) *
        Real.exp (C + (1 + η) * exponentialIntegral (δ * Real.log R) +
          (1 + η) * Real.exp 1 * Real.log (1 / δ)) := by
  obtain ⟨C, hC, he⟩ := uniform_euler_upper η hη
  refine ⟨C, hC, ?_⟩
  intro X δ R hδ hδhalf hR
  have hY : 2 ≤ ⌊R⌋₊ := (Nat.le_floor_iff (by linarith only [hR] : 0 ≤ R)).mpr (by exact_mod_cast hR)
  have hsub : ((OddPrimePivot.pivotValues X ⌊R⌋₊).card : ℝ) ≤ (SmallKernelCount.smallKernelValues ⌊R⌋₊ 1 X).card := by
    exact_mod_cast Finset.card_le_card (PolylogPivotExceptions.pivot_subset_small_kernel X ⌊R⌋₊ (by omega))
  have hbase := SmallKernelCount.card_smallKernelValues_le_euler ⌊R⌋₊ 1 X (1 - δ) (by linarith only [hδhalf])
  have hone : PartialPowerSum.powerSum (1 - δ) 1 = 1 := by simp [PartialPowerSum.powerSum]
  rw [hone, mul_one] at hbase
  exact hsub.trans (hbase.trans (mul_le_mul_of_nonneg_left (he δ R hδ hδhalf hR)
    (Real.rpow_nonneg (Nat.cast_nonneg X) _)))

end PaperP1.ExponentialIntegralPowerLog
