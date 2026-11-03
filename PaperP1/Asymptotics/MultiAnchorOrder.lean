module

public import PaperP1.Arithmetic.MultiAnchorPrimeBudget
public import PaperP1.Asymptotics.ModerateOrder

/-! # Growing ceiling orders for t-anchor moderate certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorOrder

open Filter

abbrev cutoff := PaperP1.ModerateOrder.cutoff

def order (t : ℕ) (A : ℝ) (N : ℕ) : ℕ := PaperP1.MultiAnchorPrimeBudget.assignmentExponent t N (cutoff A N)

def rawOrder (t : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  (t : ℝ) * Real.log (3 * (N : ℝ)) / (A * Real.log (Real.log N))

def scaledOrder (t : ℕ) (A : ℝ) (N : ℕ) : ℝ :=
  (order t A N : ℝ) * Real.log (Real.log N) / Real.log N

theorem order_eq_ceil (t : ℕ) (A : ℝ) (N : ℕ) (hN : 0 < Real.log N) : order t A N = ⌈rawOrder t A N⌉₊ := by
  unfold order cutoff PaperP1.ModerateOrder.cutoff rawOrder
    PaperP1.MultiAnchorPrimeBudget.assignmentExponent
  rw [Real.log_rpow hN A]

theorem loglog_tendsto_atTop : Tendsto (fun N : ℕ ↦ Real.log (Real.log N)) atTop atTop :=
  Real.tendsto_log_atTop.comp PaperP1.PrimeLogBudget.log_nat_tendsto_atTop

theorem loglog_div_log_tendsto_zero :
    Tendsto (fun N : ℕ ↦ Real.log (Real.log N) / Real.log N) atTop (nhds 0) := by
  have h := (PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one).comp
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  simpa only [Real.rpow_one, Function.comp_def] using h

theorem scaledOrder_bounds_eventually (t : ℕ) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      ((t : ℝ) / A) * (Real.log (3 * (N : ℝ)) / Real.log N) ≤ scaledOrder t A N ∧
      scaledOrder t A N ≤ ((t : ℝ) / A) * (Real.log (3 * (N : ℝ)) / Real.log N) +
        Real.log (Real.log N) / Real.log N := by
  filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 2] with N hH hN
  have hHpos : 0 < Real.log N := by linarith
  have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog3 : 0 ≤ Real.log (3 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hraw : 0 ≤ rawOrder t A N := by unfold rawOrder; positivity
  have hlower : rawOrder t A N ≤ (order t A N : ℝ) := by
    rw [order_eq_ceil t A N hHpos]
    exact Nat.le_ceil _
  have hupper : (order t A N : ℝ) ≤ rawOrder t A N + 1 := by
    rw [order_eq_ceil t A N hHpos]
    exact (Nat.ceil_lt_add_one hraw).le
  have hnorm : rawOrder t A N * Real.log (Real.log N) / Real.log N =
      ((t : ℝ) / A) * (Real.log (3 * (N : ℝ)) / Real.log N) := by
    unfold rawOrder
    field_simp
  constructor
  · calc
      _ = rawOrder t A N * Real.log (Real.log N) / Real.log N := hnorm.symm
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlower hlogH.le) hHpos.le
  · calc
      _ ≤ (rawOrder t A N + 1) * Real.log (Real.log N) / Real.log N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hupper hlogH.le) hHpos.le
      _ = rawOrder t A N * Real.log (Real.log N) / Real.log N + Real.log (Real.log N) / Real.log N := by ring
      _ = _ := by rw [hnorm]

theorem scaledOrder_tendsto (t : ℕ) (A : ℝ) (hA : 0 < A) :
    Tendsto (scaledOrder t A) atTop (nhds ((t : ℝ) / A)) := by
  have hlow : Tendsto (fun N : ℕ ↦ ((t : ℝ) / A) * (Real.log (3 * (N : ℝ)) / Real.log N))
      atTop (nhds ((t : ℝ) / A)) := by
    simpa only [mul_one] using (tendsto_const_nhds.mul
      (PaperP1.PrimeLogBudget.log_mul_div_log_tendsto 3 (by norm_num)))
  have hupp := hlow.add loglog_div_log_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow (by simpa only [add_zero] using hupp)
  · exact (scaledOrder_bounds_eventually t A hA).mono fun _ h ↦ h.1
  · exact (scaledOrder_bounds_eventually t A hA).mono fun _ h ↦ h.2

theorem order_div_log_tendsto_zero (t : ℕ) (A : ℝ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ (order t A N : ℝ) / Real.log N) atTop (nhds 0) := by
  have hinv := tendsto_inv_atTop_zero.comp loglog_tendsto_atTop
  have hlim := (scaledOrder_tendsto t A hA).mul hinv
  have heq : (fun N : ℕ ↦ scaledOrder t A N * (Real.log (Real.log N))⁻¹) =ᶠ[atTop]
      (fun N : ℕ ↦ (order t A N : ℝ) / Real.log N) := by
    filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hH
    have hHpos : 0 < Real.log N := by linarith
    have hlogH : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
    unfold scaledOrder
    field_simp
  exact Tendsto.congr' heq (by simpa only [mul_zero, Function.comp_def] using hlim)

theorem order_le_log_eventually (t : ℕ) (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop, (order t A N : ℝ) ≤ Real.log N := by
  have hsmall := (order_div_log_tendsto_zero t A hA).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N h hH
  have hHpos : 0 < Real.log N := by linarith
  have h' := (div_lt_iff₀ hHpos).mp h
  linarith

end PaperP1.MultiAnchorOrder
