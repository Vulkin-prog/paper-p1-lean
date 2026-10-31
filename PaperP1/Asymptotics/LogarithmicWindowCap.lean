module

public import PaperP1.Arithmetic.PrimeLogBudget

/-!
# A common logarithmic window cap

The integer length `ceil(c log N)` has the exact leading coefficient c.
Its prime budget therefore has leading coefficient c after normalization
by log N. These limits are independent of any choice of window base.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicWindowCap

open Filter Real PrimeLogBudget LocalDefectBound

def cap (c : ℝ) (N : ℕ) : ℕ := ⌈c * Real.log N⌉₊

theorem cap_div_log_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ ↦ (cap c N : ℝ) / Real.log N) atTop (nhds c) := by
  have hinv := tendsto_inv_atTop_zero.comp log_nat_tendsto_atTop
  have hupperlim : Tendsto (fun N : ℕ ↦ c + (Real.log N)⁻¹) atTop (nhds c) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hinv :
      Tendsto (fun N : ℕ ↦ c + (Real.log N)⁻¹) atTop (nhds (c + 0)))
  have hlower : ∀ᶠ N : ℕ in atTop, c ≤ (cap c N : ℝ) / Real.log N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    exact (le_div_iff₀ hlog).mpr (Nat.le_ceil _)
  have hupper : ∀ᶠ N : ℕ in atTop,
      (cap c N : ℝ) / Real.log N ≤ c + (Real.log N)⁻¹ := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    apply (div_le_iff₀ hlog).mpr
    rw [add_mul, inv_mul_cancel₀ hlog.ne']
    exact (Nat.ceil_lt_add_one (mul_nonneg hc hlog.le)).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperlim hlower hupper

theorem cap_tendsto_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (cap c) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hmul : Tendsto (fun N : ℕ ↦ c * Real.log N) atTop atTop :=
    Tendsto.const_mul_atTop hc log_nat_tendsto_atTop
  filter_upwards [hmul.eventually (eventually_ge_atTop (b : ℝ))] with N hN
  have h : (b : ℝ) ≤ (cap c N : ℝ) := hN.trans (Nat.le_ceil _)
  exact_mod_cast h

theorem cap_div_nat_tendsto (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ ↦ (cap c N : ℝ) / N) atTop (nhds 0) := by
  have hprod := (cap_div_log_tendsto c hc).mul log_nat_div_self_tendsto
  have heq : (fun N : ℕ ↦ (cap c N : ℝ) / N) =ᶠ[atTop]
      (fun N : ℕ ↦ ((cap c N : ℝ) / Real.log N) * (Real.log N / N)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    field_simp [hn.ne', hl.ne']
  exact Tendsto.congr' heq.symm (by simpa only [mul_zero] using hprod)

/-- The PNT budget at the common rounded cap has the original leading coefficient c. -/
theorem cap_prime_budget_tendsto (c : ℝ) (hc : 0 < c) (t : ℕ) :
    Tendsto (fun N : ℕ ↦ ((primeCount (cap c N) : ℝ) + 1 + t) *
      Real.log (64 * (cap c N : ℝ)) / Real.log N) atTop (nhds c) := by
  have hprime := (prime_log_budget_ratio_tendsto t).comp (cap_tendsto_atTop c hc)
  have hprod := hprime.mul (cap_div_log_tendsto c hc.le)
  have heq : (fun N : ℕ ↦ ((primeCount (cap c N) : ℝ) + 1 + t) *
      Real.log (64 * (cap c N : ℝ)) / Real.log N) =ᶠ[atTop]
      (fun N : ℕ ↦
        (((primeCount (cap c N) : ℝ) + 1 + t) *
          Real.log (64 * (cap c N : ℝ)) / (cap c N : ℝ)) *
        ((cap c N : ℝ) / Real.log N)) := by
    filter_upwards [(cap_tendsto_atTop c hc).eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 2] with N hcap hN
    have hcapR : (0 : ℝ) < cap c N := by exact_mod_cast (show 0 < cap c N by omega)
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    field_simp [hcapR.ne', hl.ne']
  exact Tendsto.congr' heq.symm (by simpa only [one_mul, Function.comp_def] using hprod)

end PaperP1.LogarithmicWindowCap
