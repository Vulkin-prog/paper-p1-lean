module

public import PaperP1.Asymptotics.ModerateOrder

/-! # The uniform exponential budget for saturation degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SaturationDegreeBudget

open Filter PaperP1.ModerateOrder

def envelope (A D K J : ℝ) (N : ℕ) : ℝ :=
  ((order A N : ℝ) + 2) * (Real.log (Real.log N) + Real.log D) +
    (order A N : ℝ) * Real.log K + Real.log J

theorem envelope_div_log_tendsto (A D K J : ℝ) (hA : 0 < A) :
    Tendsto (fun N : ℕ ↦ envelope A D K J N / Real.log N) atTop (nhds (2 / A)) := by
  have hinv : Tendsto (fun N : ℕ ↦ (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have hlim := ((scaledOrder_tendsto A hA).add (loglog_div_log_tendsto_zero.const_mul 2)).add
    (((order_div_log_tendsto_zero A hA).const_mul (Real.log D + Real.log K)).add
      (hinv.const_mul (2 * Real.log D + Real.log J)))
  have hidentity (N : ℕ) : envelope A D K J N / Real.log N =
      scaledOrder A N + 2 * (Real.log (Real.log N) / Real.log N) +
        ((Real.log D + Real.log K) * ((order A N : ℝ) / Real.log N) +
          (2 * Real.log D + Real.log J) * (Real.log N)⁻¹) := by
    unfold envelope scaledOrder
    ring
  simp_rw [hidentity]
  simpa only [mul_zero, add_zero] using hlim

theorem log_product_le_envelope (A D K J : ℝ) (N B : ℕ)
    (hH : 0 < Real.log N) (hD : 0 < D) (hK : 0 < K) (hJ : 0 < J) (hB : 1 ≤ B)
    (hwidth : (B : ℝ) ≤ D * Real.log N) :
    Real.log (J * (B : ℝ) ^ 2 * (K * B) ^ order A N) ≤ envelope A D K J N := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : Real.log B ≤ Real.log (Real.log N) + Real.log D := by
    have h := Real.log_le_log hBpos hwidth
    rw [Real.log_mul hD.ne' hH.ne'] at h
    linarith
  rw [Real.log_mul (by positivity : J * (B : ℝ) ^ 2 ≠ 0) (by positivity : (K * (B : ℝ)) ^ order A N ≠ 0),
    Real.log_mul hJ.ne' (by positivity : (B : ℝ) ^ 2 ≠ 0), Real.log_pow, Real.log_pow,
    Real.log_mul hK.ne' hBpos.ne']
  have h := mul_le_mul_of_nonneg_left hlogB (by positivity : (0 : ℝ) ≤ (order A N : ℝ) + 2)
  unfold envelope
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem product_le_power_eventually (A D K J ε : ℝ)
    (hA : 0 < A) (hD : 1 ≤ D) (hK : 0 < K) (hJ : 0 < J) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      J * (B : ℝ) ^ 2 * (K * B) ^ order A N ≤ (N : ℝ) ^ (2 / A + ε) := by
  have hlim := (envelope_div_log_tendsto A D K J hA).eventually
    (eventually_lt_nhds (by linarith : 2 / A < 2 / A + ε))
  filter_upwards [hlim, PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N henv hH hN B hB hwidth
  have hHpos : 0 < Real.log N := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog := log_product_le_envelope A D K J N B hHpos (by linarith) hK hJ hB hwidth
  have hbound := (div_lt_iff₀ hHpos).mp henv
  rw [Real.rpow_def_of_pos hNpos]
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  linarith

end PaperP1.SaturationDegreeBudget
