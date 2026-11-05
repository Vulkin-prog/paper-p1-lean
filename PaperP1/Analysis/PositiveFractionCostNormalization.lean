module

public import PaperP1.Analysis.CleanPairReciprocalLower

/-! # A fixed positive source fraction suffices for a fixed positive cost fraction -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.PositiveFractionCostNormalization

theorem with_errors {n j c z Q δ e₁ e₂ : ℝ} (hn : 0 ≤ n) (hQ : 0 < Q)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hct : c / z ≤ 1 / 4)
    (hjlo : δ * n ≤ j) (hjhi : j ≤ n)
    (he : (c + 1) * n + e₁ + e₂ ≤ δ / 4 * (n ^ 2 / Q)) :
    δ / 2 * (n ^ 2 / Q) ≤
      (1 - c / z) * n * (j / Q) - (c + 1) * j - e₁ - e₂ := by
  have hcoef : (3 / 4 : ℝ) ≤ 1 - c / z := by linarith only [hct]
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hcoef hn)
    (div_le_div_of_nonneg_right hjlo hQ.le) (div_nonneg (mul_nonneg hδ hn) hQ.le)
    (mul_nonneg (by linarith only [hcoef] : 0 ≤ 1 - c / z) hn)
  have hmain : (3 * δ / 4) * (n ^ 2 / Q) ≤ (1 - c / z) * n * (j / Q) := by
    convert hm using 1
    ring
  have hcost := mul_le_mul_of_nonneg_left hjhi (by linarith only [hc] : 0 ≤ c + 1)
  nlinarith only [hmain, hcost, he]

end PaperP1.PositiveFractionCostNormalization
