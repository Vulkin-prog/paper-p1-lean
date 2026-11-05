module

public import PaperP1.Analysis.SmoothLowerBarrierProfile

/-! # The strict prime-weight margin of the smooth lower barrier

The limiting margin is exp(epsilon)>1, leaving room for the true-leading
prime estimate and the actual integer quotient loss.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothLowerBarrierGrowth

open Set Filter SmoothLowerBarrierProfile

def primeMargin (ε t : ℝ) : ℝ :=
  (Real.exp (tilt ε (t - 1)) - 2) / (t * tilt ε (t - 1))

theorem tendsto_loglog_div_log :
    Tendsto (fun t : ℝ ↦ Real.log (Real.log t) / Real.log t) atTop (nhds 0) := by
  have ht : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  simpa only [Function.comp_def] using ht.comp Real.tendsto_log_atTop

theorem tendsto_tilt_div_log (ε : ℝ) :
    Tendsto (fun t : ℝ ↦ tilt ε t / Real.log t) atTop (nhds 1) := by
  have hc : Tendsto (fun t : ℝ ↦ ε / Real.log t) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have ht : Tendsto (fun t : ℝ ↦ 1 + Real.log (Real.log t) / Real.log t + ε / Real.log t)
      atTop (nhds 1) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_loglog_div_log).add hc
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  dsimp only [tilt]
  field_simp

theorem tendsto_log_div_tilt (ε : ℝ) :
    Tendsto (fun t : ℝ ↦ Real.log t / tilt ε t) atTop (nhds 1) := by
  have ht := (tendsto_tilt_div_log ε).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun _ ↦ by simp only [inv_div])

theorem exp_tilt (ε t : ℝ) (ht : 1 < t) :
    Real.exp (tilt ε t) = Real.exp ε * t * Real.log t := by
  have ht0 : 0 < t := by linarith only [ht]
  rw [tilt, Real.exp_add, Real.exp_add, Real.exp_log ht0, Real.exp_log (Real.log_pos ht)]
  ring

theorem tendsto_tilt_atTop (ε : ℝ) : Tendsto (tilt ε) atTop atTop := by
  have ht := Real.tendsto_log_atTop.atTop_add_atTop (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply (tendsto_atTop_add_const_right atTop ε ht).congr'
  exact Eventually.of_forall (fun _ ↦ rfl)

theorem tendsto_primeMargin (ε : ℝ) : Tendsto (primeMargin ε) atTop (nhds (Real.exp ε)) := by
  have hshift : Tendsto (fun t : ℝ ↦ t - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  have ha : Tendsto (fun t : ℝ ↦ (t - 1) / t) atTop (nhds 1) := by
    have hi : Tendsto (fun t : ℝ ↦ (1 : ℝ) / t) atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
    have ht : Tendsto (fun t : ℝ ↦ 1 - 1 / t) atTop (nhds 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp
  have hb := (tendsto_log_div_tilt ε).comp hshift
  have htilt := (tendsto_tilt_atTop ε).comp hshift
  have hden := tendsto_id.atTop_mul_atTop₀ htilt
  have hc : Tendsto (fun t : ℝ ↦ 2 / (t * tilt ε (t - 1))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have ht : Tendsto (fun t : ℝ ↦ Real.exp ε * ((t - 1) / t) *
      (Real.log (t - 1) / tilt ε (t - 1)) - 2 / (t * tilt ε (t - 1)))
      atTop (nhds (Real.exp ε)) := by
    simpa only [Function.comp_def, mul_one, sub_zero] using ((ha.const_mul (Real.exp ε)).mul hb).sub hc
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ), htilt.eventually (eventually_ge_atTop (1 : ℝ))] with t ht hξ
  have ht0 : t ≠ 0 := by linarith only [ht]
  have hξ0 : tilt ε (t - 1) ≠ 0 := by change 1 ≤ tilt ε (t - 1) at hξ; linarith only [hξ]
  rw [primeMargin, exp_tilt ε (t - 1) (by linarith only [ht])]
  field_simp

theorem uniform_margin (ε : ℝ) (hε : 0 < ε) :
    ∃ m T : ℝ, 1 < m ∧ Real.exp 1 ≤ T ∧ ∀ t ≥ T, m ≤ primeMargin ε t := by
  have he : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
  let m := (1 + Real.exp ε) / 2
  have hm : 1 < m := by dsimp only [m]; linarith only [he]
  have hme : m < Real.exp ε := by dsimp only [m]; linarith only [he]
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((tendsto_primeMargin ε).eventually (eventually_gt_nhds hme))
  refine ⟨m, max T (Real.exp 1), hm, le_max_right _ _, ?_⟩
  intro t ht
  exact (hT t ((le_max_left _ _).trans ht)).le

end PaperP1.SmoothLowerBarrierGrowth
