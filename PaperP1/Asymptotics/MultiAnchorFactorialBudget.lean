module

public import PaperP1.Asymptotics.MultiAnchorOrder
public import PaperP1.Asymptotics.FactorialLogBounds

/-! # Uniform factorial budgets for t-anchor certificate orders -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorFactorialBudget

open Filter PaperP1.MultiAnchorOrder

def envelope (t : ℕ) (A D : ℝ) (N : ℕ) : ℝ :=
  ((order t A N : ℝ) + 2 * t) * (Real.log (Real.log N) + Real.log D) +
    ((order t A N : ℝ) + 1) * (Real.log (Real.log N) + Real.log 2)

theorem envelope_div_log_tendsto (t : ℕ) (A D : ℝ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ envelope t A D N / Real.log N) atTop (nhds (2 * (t : ℝ) / A)) := by
  have hinv : Tendsto (fun N : ℕ ↦ (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have hlim := (((scaledOrder_tendsto t A hA).const_mul 2).add
    ((order_div_log_tendsto_zero t A hA).const_mul (Real.log D + Real.log 2))).add
    ((loglog_div_log_tendsto_zero.const_mul (2 * (t : ℝ) + 1)).add
      (hinv.const_mul (2 * t * Real.log D + Real.log 2)))
  have hidentity (N : ℕ) : envelope t A D N / Real.log N =
      2 * scaledOrder t A N + (Real.log D + Real.log 2) * ((order t A N : ℝ) / Real.log N) +
        ((2 * t + 1) * (Real.log (Real.log N) / Real.log N) +
          (2 * t * Real.log D + Real.log 2) * (Real.log N)⁻¹) := by
    unfold envelope scaledOrder
    ring
  simp_rw [hidentity]
  convert hlim using 1; ring

theorem log_product_le_envelope (t : ℕ) (A D : ℝ) (N B : ℕ)
    (hH : 2 ≤ Real.log N) (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hwidth : (B : ℝ) ≤ D * Real.log N) (hm : (order t A N : ℝ) ≤ Real.log N) :
    Real.log ((B : ℝ) ^ (order t A N + 2 * t) * ((order t A N + 1).factorial : ℝ)) ≤
      envelope t A D N := by
  have hHpos : 0 < Real.log N := by linarith
  have hDpos : 0 < D := by linarith
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : Real.log B ≤ Real.log (Real.log N) + Real.log D := by
    have h := Real.log_le_log hBpos hwidth
    rw [Real.log_mul hDpos.ne' hHpos.ne'] at h
    linarith
  have horder : ((order t A N + 1 : ℕ) : ℝ) ≤ 2 * Real.log N := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hlogOrder : Real.log ((order t A N + 1 : ℕ) : ℝ) ≤ Real.log (Real.log N) + Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((order t A N + 1 : ℕ) : ℝ)) horder
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHpos.ne'] at h
    linarith
  have hfac := (PaperP1.FactorialLogBounds.log_factorial_bounds (order t A N + 1) (by omega)).2
  have hfac' := hfac.trans (mul_le_mul_of_nonneg_left hlogOrder
    (by positivity : (0 : ℝ) ≤ ((order t A N + 1 : ℕ) : ℝ)))
  rw [Real.log_mul (by positivity : (B : ℝ) ^ (order t A N + 2 * t) ≠ 0)
    (by positivity : ((order t A N + 1).factorial : ℝ) ≠ 0), Real.log_pow]
  have hfirst := mul_le_mul_of_nonneg_left hlogB
    (by positivity : (0 : ℝ) ≤ ((order t A N + 2 * t : ℕ) : ℝ))
  unfold envelope
  push_cast at hfirst hfac' ⊢
  linarith

/-- The threshold is chosen before every window width B. -/
theorem product_le_power_eventually (t : ℕ) (A D ε : ℝ) (hA : 0 < A) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      (B : ℝ) ^ (order t A N + 2 * t) * ((order t A N + 1).factorial : ℝ) ≤
        (N : ℝ) ^ (2 * (t : ℝ) / A + ε) := by
  have hlim := (envelope_div_log_tendsto t A D hA).eventually
    (eventually_lt_nhds (by linarith : 2 * (t : ℝ) / A < 2 * (t : ℝ) / A + ε))
  filter_upwards [hlim, order_le_log_eventually t A hA,
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N henv hm hH hN B hB hwidth
  have hHpos : 0 < Real.log N := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog := log_product_le_envelope t A D N B hH hD hB hwidth hm
  have hbound := (div_lt_iff₀ hHpos).mp henv
  rw [Real.rpow_def_of_pos hNpos]
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  linarith

end PaperP1.MultiAnchorFactorialBudget
