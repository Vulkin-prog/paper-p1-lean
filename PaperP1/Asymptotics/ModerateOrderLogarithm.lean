module

public import PaperP1.Asymptotics.ModerateOrder

/-! # The logarithm and logarithmic cost of a growing trial order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateOrderLogarithm

open Filter PaperP1.ModerateOrder

theorem order_pos_eventually (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, 0 < (order A N : ℝ) := by
  filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N hH hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hHpos : 0 < Real.log N := by linarith
  have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hlog3 : 0 < Real.log (3 * (N : ℝ)) := Real.log_pos (by linarith)
  have hraw : 0 < rawOrder A N := by unfold rawOrder; positivity
  exact hraw.trans_le (by rw [order_eq_ceil A N hHpos]; exact Nat.le_ceil _)

theorem log_order_ratio_tendsto (A : ℝ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ Real.log (order A N : ℝ) / Real.log (Real.log N)) atTop (nhds 1) := by
  have hthird : Tendsto (fun N : ℕ ↦ Real.log (Real.log (Real.log N)) / Real.log (Real.log N))
      atTop (nhds 0) := by
    have h := (PaperP1.PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one).comp loglog_tendsto_atTop
    simpa only [Real.rpow_one, Function.comp_def] using h
  have hlogscaled := (scaledOrder_tendsto A hA).log (div_ne_zero (by norm_num) hA.ne')
  have hsmall : Tendsto (fun N : ℕ ↦ Real.log (scaledOrder A N) / Real.log (Real.log N))
      atTop (nhds 0) := by
    have h := hlogscaled.mul (tendsto_inv_atTop_zero.comp loglog_tendsto_atTop)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using h
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlim := (hone.sub hthird).add hsmall
  have heq : (fun N : ℕ ↦ Real.log (order A N : ℝ) / Real.log (Real.log N)) =ᶠ[atTop]
      (fun N : ℕ ↦ 1 - Real.log (Real.log (Real.log N)) / Real.log (Real.log N) +
        Real.log (scaledOrder A N) / Real.log (Real.log N)) := by
    filter_upwards [order_pos_eventually A hA,
      PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hK hH
    have hHpos : 0 < Real.log N := by linarith
    have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
    have hlog : Real.log (scaledOrder A N) = Real.log (order A N : ℝ) +
        Real.log (Real.log (Real.log N)) - Real.log (Real.log N) := by
      rw [scaledOrder, Real.log_div (mul_ne_zero hK.ne' hlogH.ne') hHpos.ne',
        Real.log_mul hK.ne' hlogH.ne']
    rw [hlog]
    field_simp
    ring
  exact Tendsto.congr' heq.symm (by simpa only [sub_zero, add_zero] using hlim)

theorem order_real_tendsto_atTop (A : ℝ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ (order A N : ℝ)) atTop atTop := by
  have hprod := (log_order_ratio_tendsto A hA).pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
    loglog_tendsto_atTop
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (order A N : ℝ)) atTop atTop := by
    apply Tendsto.congr' _ hprod
    filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hH
    have hlogH : Real.log (Real.log N) ≠ 0 := (Real.log_pos (by linarith : 1 < Real.log N)).ne'
    exact div_mul_cancel₀ _ hlogH
  have hexp := Real.tendsto_exp_atTop.comp hlog
  apply Tendsto.congr' _ hexp
  filter_upwards [order_pos_eventually A hA] with N hK
  exact Real.exp_log hK

theorem logarithmic_cost_tendsto (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    Tendsto (fun N : ℕ ↦ (order A N : ℝ) * Real.log ((order A N : ℝ) / c) / Real.log N)
      atTop (nhds (2 / A)) := by
  have hcsmall : Tendsto (fun N : ℕ ↦ Real.log c / Real.log (Real.log N)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Real.log c) atTop (nhds (Real.log c)) := tendsto_const_nhds
    have h := hconst.mul (tendsto_inv_atTop_zero.comp loglog_tendsto_atTop)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using h
  have hlim := (scaledOrder_tendsto A hA).mul ((log_order_ratio_tendsto A hA).sub hcsmall)
  have heq : (fun N : ℕ ↦ (order A N : ℝ) * Real.log ((order A N : ℝ) / c) / Real.log N) =ᶠ[atTop]
      (fun N : ℕ ↦ scaledOrder A N * (Real.log (order A N : ℝ) / Real.log (Real.log N) -
        Real.log c / Real.log (Real.log N))) := by
    filter_upwards [order_pos_eventually A hA,
      PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hK hH
    have hlogH : Real.log (Real.log N) ≠ 0 := (Real.log_pos (by linarith : 1 < Real.log N)).ne'
    rw [Real.log_div hK.ne' hc.ne']
    unfold scaledOrder
    field_simp
  exact Tendsto.congr' heq.symm (by simpa only [sub_zero, mul_one] using hlim)

end PaperP1.ModerateOrderLogarithm
