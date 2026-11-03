module

public import PaperP1.Asymptotics.MultiAnchorOrder

/-! # Fixed-order anchor budgets with an arbitrary polynomial prefactor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedAnchorDegreeBudget

open Filter PaperP1.MultiAnchorOrder

def envelope (t k : ℕ) (A D K J : ℝ) (N : ℕ) : ℝ :=
  ((order t A N : ℝ) + k) * (Real.log (Real.log N) + Real.log D) +
    (order t A N : ℝ) * Real.log K + Real.log J

theorem envelope_div_log_tendsto (t k : ℕ) (A D K J : ℝ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ envelope t k A D K J N / Real.log N) atTop (nhds ((t : ℝ) / A)) := by
  have hinv : Tendsto (fun N : ℕ ↦ (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have hlim := ((scaledOrder_tendsto t A hA).add (loglog_div_log_tendsto_zero.const_mul (k : ℝ))).add
    (((order_div_log_tendsto_zero t A hA).const_mul (Real.log D + Real.log K)).add
      (hinv.const_mul ((k : ℝ) * Real.log D + Real.log J)))
  have hidentity (N : ℕ) : envelope t k A D K J N / Real.log N =
      scaledOrder t A N + (k : ℝ) * (Real.log (Real.log N) / Real.log N) +
        ((Real.log D + Real.log K) * ((order t A N : ℝ) / Real.log N) +
          ((k : ℝ) * Real.log D + Real.log J) * (Real.log N)⁻¹) := by
    unfold envelope scaledOrder
    ring
  simp_rw [hidentity]
  simpa only [mul_zero, add_zero] using hlim

theorem log_product_le_envelope (t k : ℕ) (A D K J : ℝ) (N B : ℕ)
    (hH : 0 < Real.log N) (hD : 0 < D) (hK : 0 < K) (hJ : 0 < J) (hB : 1 ≤ B)
    (hwidth : (B : ℝ) ≤ D * Real.log N) :
    Real.log (J * (B : ℝ) ^ k * (K * B) ^ order t A N) ≤ envelope t k A D K J N := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : Real.log B ≤ Real.log (Real.log N) + Real.log D := by
    have h := Real.log_le_log hBpos hwidth
    rw [Real.log_mul hD.ne' hH.ne'] at h
    linarith
  rw [Real.log_mul (by positivity : J * (B : ℝ) ^ k ≠ 0) (by positivity : (K * (B : ℝ)) ^ order t A N ≠ 0),
    Real.log_mul hJ.ne' (by positivity : (B : ℝ) ^ k ≠ 0), Real.log_pow, Real.log_pow,
    Real.log_mul hK.ne' hBpos.ne']
  have h := mul_le_mul_of_nonneg_left hlogB (by positivity : (0 : ℝ) ≤ (order t A N : ℝ) + k)
  unfold envelope
  nlinarith

theorem product_le_power_eventually (t k : ℕ) (A D K J ε : ℝ)
    (hA : 0 < A) (hD : 1 ≤ D) (hK : 0 < K) (hJ : 0 < J) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      J * (B : ℝ) ^ k * (K * B) ^ order t A N ≤ (N : ℝ) ^ ((t : ℝ) / A + ε) := by
  have hlim := (envelope_div_log_tendsto t k A D K J hA).eventually
    (eventually_lt_nhds (by linarith : (t : ℝ) / A < (t : ℝ) / A + ε))
  filter_upwards [hlim, PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N henv hH hN B hB hwidth
  have hHpos : 0 < Real.log N := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog := log_product_le_envelope t k A D K J N B hHpos (by linarith) hK hJ hB hwidth
  have hbound := (div_lt_iff₀ hHpos).mp henv
  rw [Real.rpow_def_of_pos hNpos]
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  linarith

end PaperP1.FixedAnchorDegreeBudget
