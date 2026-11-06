module

public import PaperP1.Analysis.LogarithmicShiftPhase
public import PaperP1.Analysis.ReciprocalFiniteDifferences

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ReciprocalDifferenceBounds
open MeasureTheory PaperP1 ReciprocalFiniteDifferences
open scoped Classical

theorem shifts_sum_nonneg (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) : 0 ≤ hs.sum := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    have h0 := hhs h List.mem_cons_self
    have ht : ∀ v ∈ hs, 0 ≤ v := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    simpa only [List.sum_cons] using add_nonneg h0 (ih ht)

theorem interval_integrable (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (m : ℕ)
    (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) : IntervalIntegrable (kernel hs m) volume A B := by
  have hc : ContinuousOn (kernel hs m) (Set.Icc A B) := by
    intro x hx
    exact (hasDerivAt_kernel hs hhs m x (hA.trans_le hx.1)).continuousAt.continuousWithinAt
  exact hc.intervalIntegrable_of_Icc hAB

theorem difference_integral (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (m : ℕ)
    (x h : ℝ) (hx : 0 < x) (hh : 0 ≤ h) :
    kernel (h::hs) m x=(m : ℝ)*(∫ y in x..x+h, kernel hs (m+1) y) := by
  have hab : x ≤ x+h := by linarith only [hh]
  have hint := (interval_integrable hs hhs (m+1) x (x+h) hx hab).const_mul (-(m : ℝ))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := kernel hs m)
    (f' := fun y ↦ -(m : ℝ)*kernel hs (m+1) y) (by
      intro y hy
      rw [Set.uIcc_of_le hab] at hy
      exact hasDerivAt_kernel hs hhs m y (hx.trans_le hy.1)) hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  change kernel hs m x-kernel hs m (x+h)=(m : ℝ)*(∫ y in x..x+h, kernel hs (m+1) y)
  linarith only [hFTC]

theorem kernel_bounds (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (m : ℕ) (x : ℝ) (hx : 0 < x) :
    coefficient m hs/(x+hs.sum)^(m+hs.length) ≤ kernel hs m x ∧
      kernel hs m x ≤ coefficient m hs/x^(m+hs.length) := by
  induction hs generalizing m x with
  | nil => simp [kernel,coefficient]
  | cons h hs ih =>
    have hh0 : 0 ≤ h := hhs h List.mem_cons_self
    have hTail : ∀ v ∈ hs, 0 ≤ v := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    have hSum : 0 ≤ hs.sum := shifts_sum_nonneg hs hTail
    have hCoeff : 0 ≤ coefficient (m+1) hs := coefficient_nonneg (m+1) hs hTail
    have hab : x ≤ x+h := by linarith only [hh0]
    have hint := interval_integrable hs hTail (m+1) x (x+h) hx hab
    have hLower (y : ℝ) (hy : y ∈ Set.Icc x (x+h)) :
        coefficient (m+1) hs/(x+h+hs.sum)^((m+1)+hs.length) ≤ kernel hs (m+1) y := by
      have hyp : 0 < y := hx.trans_le hy.1
      have hys : 0 < y+hs.sum := by linarith only [hyp,hSum]
      have hpow := pow_le_pow_left₀ hys.le (by linarith only [hy.2] : y+hs.sum ≤ x+h+hs.sum) ((m+1)+hs.length)
      exact (div_le_div_of_nonneg_left hCoeff (pow_pos hys _) hpow).trans (ih hTail (m+1) y hyp).1
    have hUpper (y : ℝ) (hy : y ∈ Set.Icc x (x+h)) :
        kernel hs (m+1) y ≤ coefficient (m+1) hs/x^((m+1)+hs.length) := by
      have hyp : 0 < y := hx.trans_le hy.1
      have hpow := pow_le_pow_left₀ hx.le hy.1 ((m+1)+hs.length)
      exact (ih hTail (m+1) y hyp).2.trans (div_le_div_of_nonneg_left hCoeff (pow_pos hx _) hpow)
    have hLI := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const hint hLower
    have hUI := intervalIntegral.integral_mono_on (μ := volume) hab hint intervalIntegrable_const hUpper
    rw [intervalIntegral.integral_const] at hLI hUI
    simp only [smul_eq_mul] at hLI hUI
    have hLm := mul_le_mul_of_nonneg_left hLI (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hUm := mul_le_mul_of_nonneg_left hUI (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    rw [← difference_integral hs hTail m x h hx hh0] at hLm hUm
    have hExp : m+(h::hs).length=(m+1)+hs.length := by simp only [List.length_cons]; omega
    constructor
    · rw [hExp]
      calc
        _ = (m : ℝ)*((x+h-x)*(coefficient (m+1) hs/(x+h+hs.sum)^((m+1)+hs.length))) := by
          simp only [coefficient,List.sum_cons]
          rw [add_assoc x h hs.sum]
          ring
        _ ≤ _ := hLm
    · rw [hExp]
      calc
        _ ≤ (m : ℝ)*((x+h-x)*(coefficient (m+1) hs/x^((m+1)+hs.length))) := hUm
        _ = _ := by simp only [coefficient]; ring
end PaperP1.ReciprocalDifferenceBounds
