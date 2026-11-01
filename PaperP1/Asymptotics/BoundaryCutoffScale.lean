module

public import PaperP1.Asymptotics.BoundaryCutoffTrial

/-! # The source least cutoff is asymptotic to three logarithmic orders -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundaryCutoffScale

open Filter PaperP1.ModerateOrder PaperP1.BoundaryCutoff PaperP1.BoundaryCutoffTrial

def scaled (Λ : ℝ) (hΛ : 0 < Λ) (N : ℕ) : ℝ :=
  (cutoff Λ hΛ N : ℝ) * Real.log (Real.log N) / Real.log N

def lowerBound (Λ : ℝ) (N : ℕ) : ℝ :=
  3 / (1 + |Real.log (2 * Real.exp 1 * Λ)| / Real.log (Real.log N))

theorem lowerBound_tendsto (Λ : ℝ) : Tendsto (lowerBound Λ) atTop (nhds 3) := by
  change Tendsto (fun N : ℕ ↦ 3 / (1 + |Real.log (2 * Real.exp 1 * Λ)| / Real.log (Real.log N))) atTop (nhds 3)
  have hsmall : Tendsto (fun N : ℕ ↦ |Real.log (2 * Real.exp 1 * Λ)| / Real.log (Real.log N))
      atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp loglog_tendsto_atTop).const_mul |Real.log (2 * Real.exp 1 * Λ)|
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using h
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hthree : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (nhds 3) := tendsto_const_nhds
  have h := hthree.div (hone.add hsmall) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  change Tendsto (fun N : ℕ ↦ 3 / (1 + |Real.log (2 * Real.exp 1 * Λ)| / Real.log (Real.log N)))
    atTop (nhds (3 / (1 + 0) : ℝ)) at h
  simpa only [add_zero, div_one] using h

theorem lowerBound_le_eventually (Λ : ℝ) (hΛ : 0 < Λ) :
    ∀ᶠ N : ℕ in atTop, lowerBound Λ N ≤ scaled Λ hΛ N := by
  have hsmall := (cutoff_div_log_tendsto Λ hΛ).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall,
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hKsmall hH
  let c : ℝ := 2 * Real.exp 1 * Λ
  have hc : 0 < c := by dsimp [c]; positivity
  have hHpos : 0 < Real.log N := by linarith
  have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hKpos : (0 : ℝ) < cutoff Λ hΛ N := by exact_mod_cast cutoff_pos Λ hΛ N
  have hKH : (cutoff Λ hΛ N : ℝ) ≤ Real.log N := (div_lt_one hHpos).mp hKsmall |>.le
  have hlogK := Real.log_le_log hKpos hKH
  have hupper : Real.log ((cutoff Λ hΛ N : ℝ) / c) ≤ Real.log (Real.log N) + |Real.log c| := by
    rw [Real.log_div hKpos.ne' hc.ne']
    linarith [neg_le_abs (Real.log c)]
  have hbudget := (cutoff_spec Λ hΛ N).2
  have hbound : 3 * Real.log N ≤ (cutoff Λ hΛ N : ℝ) * (Real.log (Real.log N) + |Real.log c|) :=
    hbudget.trans (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg _))
  have hden : 0 < 1 + |Real.log c| / Real.log (Real.log N) := by positivity
  unfold lowerBound scaled
  change 3 / (1 + |Real.log c| / Real.log (Real.log N)) ≤ _
  apply (div_le_iff₀ hden).mpr
  calc
    3 ≤ (cutoff Λ hΛ N : ℝ) * (Real.log (Real.log N) + |Real.log c|) / Real.log N :=
      (le_div_iff₀ hHpos).mpr hbound
    _ = _ := by field_simp

theorem scaled_le_trial_eventually (A Λ : ℝ) (hA : 0 < A) (hΛ : 0 < Λ) (hgap : 3 < 2 / A) :
    ∀ᶠ N : ℕ in atTop, scaled Λ hΛ N ≤ scaledOrder A N := by
  filter_upwards [cutoff_le_trial_eventually A Λ hA hΛ hgap,
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hK hH
  have hHpos : 0 < Real.log N := by linarith
  have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  unfold scaled scaledOrder
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hK) hlogH.le) hHpos.le

theorem scaled_tendsto_three (Λ : ℝ) (hΛ : 0 < Λ) : Tendsto (scaled Λ hΛ) atTop (nhds 3) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [(lowerBound_tendsto Λ).eventually (eventually_gt_nhds ha),
      lowerBound_le_eventually Λ hΛ] with N hlo hbound
    exact hlo.trans_le hbound
  · intro b hb
    let m : ℝ := (3 + b) / 2
    have hm : 3 < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    let A : ℝ := 2 / m
    have hA : 0 < A := div_pos (by norm_num) (by linarith)
    have hlimit : 2 / A = m := by dsimp [A]; field_simp
    have hgap : 3 < 2 / A := by rw [hlimit]; exact hm
    have hupper : 2 / A < b := by rw [hlimit]; exact hmb
    filter_upwards [(scaledOrder_tendsto A hA).eventually (eventually_lt_nhds hupper),
      scaled_le_trial_eventually A Λ hA hΛ hgap] with N htrial hbound
    exact hbound.trans_lt htrial

theorem cutoff_asymptotic_ratio (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (fun N : ℕ ↦ (cutoff Λ hΛ N : ℝ) / (Real.log N / Real.log (Real.log N)))
      atTop (nhds 3) := by
  have heq : (fun N : ℕ ↦ (cutoff Λ hΛ N : ℝ) / (Real.log N / Real.log (Real.log N))) =ᶠ[atTop]
      scaled Λ hΛ := by
    filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hH
    have hHpos : 0 < Real.log N := by linarith
    have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
    unfold scaled
    field_simp
  exact Tendsto.congr' heq.symm (scaled_tendsto_three Λ hΛ)

theorem cutoff_real_tendsto_atTop (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (fun N : ℕ ↦ (cutoff Λ hΛ N : ℝ)) atTop atTop := by
  have hratio := (scaled_tendsto_three Λ hΛ).div
    (scaledOrder_tendsto (1 / 2 : ℝ) (by norm_num)) (by norm_num : (2 : ℝ) / (1 / 2) ≠ 0)
  have hprod := hratio.pos_mul_atTop (by norm_num : (0 : ℝ) < 3 / (2 / (1 / 2)))
    (PaperP1.ModerateOrderLogarithm.order_real_tendsto_atTop (1 / 2 : ℝ) (by norm_num))
  apply Tendsto.congr' _ hprod
  filter_upwards [PaperP1.ModerateOrderLogarithm.order_pos_eventually (1 / 2 : ℝ) (by norm_num),
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hK hH
  have hHpos : 0 < Real.log N := by linarith
  have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  change (scaled Λ hΛ N / scaledOrder (1 / 2 : ℝ) N) * (order (1 / 2 : ℝ) N : ℝ) = _
  unfold scaled scaledOrder
  field_simp

theorem cutoff_tendsto_atTop (Λ : ℝ) (hΛ : 0 < Λ) :
    Tendsto (cutoff Λ hΛ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [(cutoff_real_tendsto_atTop Λ hΛ).eventually (eventually_ge_atTop (m : ℝ))] with N hN
  exact_mod_cast hN

end PaperP1.BoundaryCutoffScale
