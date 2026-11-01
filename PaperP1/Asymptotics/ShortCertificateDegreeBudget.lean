module

public import PaperP1.Asymptotics.ShortCertificateOrder

/-! # The sharp 1/A exponential budget for both certificate degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortCertificateDegreeBudget

open Filter PaperP1.ShortCertificateOrder

def envelope (A H D K : ℝ) (t N : ℕ) : ℝ :=
  ((upper A H N : ℝ) + t) * (Real.log (Real.log N) + Real.log D) +
    (upper A H N : ℝ) * Real.log K

theorem envelope_tendsto (A H D K : ℝ) (t : ℕ) (hA : 0 < A) (hH : 1 ≤ H) :
    Tendsto (fun N : ℕ ↦ envelope A H D K t N / Real.log N) atTop (nhds (1 / A)) := by
  have hinv : Tendsto (fun N : ℕ ↦ (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  have hlim := ((scaled_tendsto A H hA hH).add
    (PaperP1.ModerateOrder.loglog_div_log_tendsto_zero.const_mul (t : ℝ))).add
    (((upper_div_log_tendsto A H hA hH).const_mul (Real.log D + Real.log K)).add
      (hinv.const_mul ((t : ℝ) * Real.log D)))
  have hidentity (N : ℕ) : envelope A H D K t N / Real.log N =
      scaled A H N + (t : ℝ) * (Real.log (Real.log N) / Real.log N) +
        ((Real.log D + Real.log K) * ((upper A H N : ℝ) / Real.log N) +
          ((t : ℝ) * Real.log D) * (Real.log N)⁻¹) := by
    dsimp [envelope, scaled]
    ring
  simp_rw [hidentity]
  simpa only [mul_zero, add_zero] using hlim

theorem log_product_le (A H D K : ℝ) (t N B : ℕ)
    (hlog : 0 < Real.log N) (hD : 0 < D) (hK : 0 < K) (hB : 1 ≤ B)
    (hwidth : (B : ℝ) ≤ D * Real.log N) :
    Real.log ((B : ℝ) ^ t * (K * B) ^ upper A H N) ≤ envelope A H D K t N := by
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : Real.log B ≤ Real.log (Real.log N) + Real.log D := by
    have h := Real.log_le_log hb hwidth
    rw [Real.log_mul hD.ne' hlog.ne'] at h
    linarith
  rw [Real.log_mul (by positivity : (B : ℝ) ^ t ≠ 0)
      (by positivity : (K * B) ^ upper A H N ≠ 0), Real.log_pow, Real.log_pow,
    Real.log_mul hK.ne' hb.ne']
  have h := mul_le_mul_of_nonneg_left hlogB (by positivity : (0 : ℝ) ≤ (upper A H N : ℝ) + t)
  dsimp [envelope]
  nlinarith only [h]

theorem product_le_power_eventually (A H D K ε : ℝ) (t : ℕ)
    (hA : 0 < A) (hH : 1 ≤ H) (hD : 1 ≤ D) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 1 ≤ B → (B : ℝ) ≤ D * Real.log N →
      (B : ℝ) ^ t * (K * B) ^ upper A H N ≤ (N : ℝ) ^ (1 / A + ε) := by
  have hlim := (envelope_tendsto A H D K t hA hH).eventually
    (eventually_lt_nhds (by linarith : 1 / A < 1 / A + ε))
  filter_upwards [hlim, PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N henv hlog hN B hB hwidth
  have hl : 0 < Real.log N := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod := log_product_le A H D K t N B hl (by linarith) hK hB hwidth
  have hbudget := (div_lt_iff₀ hl).mp henv
  rw [Real.rpow_def_of_pos hn]
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  linarith

end PaperP1.ShortCertificateDegreeBudget
