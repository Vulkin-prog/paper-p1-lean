module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! # A quantitative logarithmic Abel window from an actual bounded summatory error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicAbelWindow

open Finset MeasureTheory intervalIntegral

def partialSum (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Icc 0 ⌊x⌋₊, c n

def weight (t : ℝ) : ℝ := t⁻¹ / Real.log t ^ 2

theorem weight_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ weight t :=
  div_nonneg (inv_nonneg.mpr ht) (sq_nonneg _)

theorem weight_continuousOn (a b : ℝ) (ha : 1 < a) : ContinuousOn weight (Set.Icc a b) := by
  have hzero (t : ℝ) (ht : t ∈ Set.Icc a b) : t ≠ 0 := by linarith [ht.1]
  have hlog (t : ℝ) (ht : t ∈ Set.Icc a b) : Real.log t ≠ 0 :=
    ne_of_gt (Real.log_pos (ha.trans_le ht.1))
  unfold weight
  fun_prop (disch := aesop)

theorem abel_identity (c : ℕ → ℝ) (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Real.log (n : ℝ))⁻¹ * c n =
      (Real.log b)⁻¹ * partialSum c b - (Real.log a)⁻¹ * partialSum c a +
        ∫ t in a..b, weight t * partialSum c t := by
  have hw : IntegrableOn weight (Set.Icc a b) volume := (weight_continuousOn a b ha).integrableOn_Icc
  have hdiff (t : ℝ) (ht : t ∈ Set.Icc a b) : DifferentiableAt ℝ (fun x ↦ (Real.log x)⁻¹) t :=
    Real.differentiableOn_inv_log.differentiableAt (Ioi_mem_nhds (ha.trans_le ht.1))
  have hd : IntegrableOn (deriv (fun t ↦ (Real.log t)⁻¹)) (Set.Icc a b) volume := by
    have hn : IntegrableOn (fun t ↦ -weight t) (Set.Icc a b) volume := hw.neg
    simpa only [Real.deriv_inv_log, weight, neg_div] using hn
  have he := sum_mul_eq_sub_sub_integral_mul c (show 0 ≤ a by linarith) hab hdiff hd
  rw [← intervalIntegral.integral_of_le hab] at he
  simpa only [partialSum, Real.deriv_inv_log, neg_div, neg_mul,
    intervalIntegral.integral_neg, sub_neg_eq_add, weight] using he

theorem weight_integral (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, weight t) = (Real.log a)⁻¹ - (Real.log b)⁻¹ :=
  integral_inv_div_log_sq ha hb

theorem logarithm_integral (a b : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, weight t * Real.log t) = Real.log (Real.log b) - Real.log (Real.log a) := by
  calc
    _ = ∫ t in a..b, t⁻¹ / Real.log t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hat : a ≤ t := (show t ∈ Set.Icc a b by simpa only [Set.uIcc_of_le hab] using ht).1
      have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (ha.trans_le hat))
      unfold weight
      field_simp
    _ = _ := integral_inv_div_log ha (ha.trans_le hab)

theorem logarithm_continuousOn (a b : ℝ) (ha : 1 < a) : ContinuousOn Real.log (Set.Icc a b) := by
  have hzero (t : ℝ) (ht : t ∈ Set.Icc a b) : t ≠ 0 := by linarith [ht.1]
  fun_prop (disch := aesop)

theorem envelope_integrable (a b h : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ weight t * (Real.log t + h)) volume a b := by
  exact ContinuousOn.intervalIntegrable_of_Icc hab
    ((weight_continuousOn a b ha).mul ((logarithm_continuousOn a b ha).add continuousOn_const))

theorem envelope_integral (a b h : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, weight t * (Real.log t + h)) = Real.log (Real.log b) - Real.log (Real.log a) +
      h * ((Real.log a)⁻¹ - (Real.log b)⁻¹) := by
  have hw : IntervalIntegrable weight volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (weight_continuousOn a b ha)
  have hl : IntervalIntegrable (fun t ↦ weight t * Real.log t) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab ((weight_continuousOn a b ha).mul (logarithm_continuousOn a b ha))
  have he : (fun t ↦ weight t * (Real.log t + h)) = (fun t ↦ weight t * Real.log t + weight t * h) := by
    funext t
    ring
  rw [he, intervalIntegral.integral_add hl (hw.mul_const h), logarithm_integral a b ha hab,
    intervalIntegral.integral_mul_const, weight_integral a b ha (ha.trans_le hab)]
  ring

theorem window_bound (c : ℕ → ℝ) (a b H : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (hbound : ∀ t ∈ Set.Icc a b, |partialSum c t - Real.log t| ≤ H) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (Real.log (n : ℝ))⁻¹ * c n) -
      (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 2 * H / Real.log a := by
  have hb : 1 < b := ha.trans_le hab
  have halog : Real.log a ≠ 0 := ne_of_gt (Real.log_pos ha)
  have hblog : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  have hia : 0 ≤ (Real.log a)⁻¹ := (inv_pos.mpr (Real.log_pos ha)).le
  have hib : 0 ≤ (Real.log b)⁻¹ := (inv_pos.mpr (Real.log_pos hb)).le
  have hca := abs_le.mp (hbound a ⟨le_rfl, hab⟩)
  have hcb := abs_le.mp (hbound b ⟨hab, le_rfl⟩)
  have hma₁ := mul_le_mul_of_nonneg_left (show Real.log a - H ≤ partialSum c a by linarith) hia
  have hma₂ := mul_le_mul_of_nonneg_left (show partialSum c a ≤ Real.log a + H by linarith) hia
  have hmb₁ := mul_le_mul_of_nonneg_left (show Real.log b - H ≤ partialSum c b by linarith) hib
  have hmb₂ := mul_le_mul_of_nonneg_left (show partialSum c b ≤ Real.log b + H by linarith) hib
  have hea : (Real.log a)⁻¹ * Real.log a = 1 := inv_mul_cancel₀ halog
  have heb : (Real.log b)⁻¹ * Real.log b = 1 := inv_mul_cancel₀ hblog
  have hw : IntegrableOn weight (Set.Icc a b) volume := (weight_continuousOn a b ha).integrableOn_Icc
  have hsum : IntervalIntegrable (fun t ↦ weight t * partialSum c t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact integrableOn_mul_sum_Icc c (m := 0) (show 0 ≤ a by linarith) hw
  have hupper := intervalIntegral.integral_mono_on hab hsum (envelope_integrable a b H ha hab)
    (fun t ht ↦ mul_le_mul_of_nonneg_left
      (show partialSum c t ≤ Real.log t + H by linarith [(abs_le.mp (hbound t ht)).2])
      (weight_nonneg t (by linarith [ht.1])))
  have hlower := intervalIntegral.integral_mono_on hab (envelope_integrable a b (-H) ha hab) hsum
    (fun t ht ↦ mul_le_mul_of_nonneg_left
      (show Real.log t + -H ≤ partialSum c t by linarith [(abs_le.mp (hbound t ht)).1])
      (weight_nonneg t (by linarith [ht.1])))
  rw [envelope_integral a b H ha hab] at hupper
  rw [envelope_integral a b (-H) ha hab] at hlower
  have he := abel_identity c a b ha hab
  rw [div_eq_mul_inv]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end PaperP1.LogarithmicAbelWindow
