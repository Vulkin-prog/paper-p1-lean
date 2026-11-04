module

public import PaperP1.Analysis.CleanPairReciprocalLower

/-! # Finite normalization of the anchored cost minorant

Only the literal source census and the proved collision/error ledger are
used. The squared retained fraction loses at most twice its deficit.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.AnchoredCostNormalization

theorem main_lower {n j c z Q t : ℝ} (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht1 : t ≤ 1) (hc : 0 ≤ c) (hct : c / z ≤ t)
    (hjlo : (1 - t) * n ≤ j) (hjhi : j ≤ n) :
    (1 - 2 * t) * n ^ 2 / Q - (c + 1) * n ≤
      (1 - c / z) * n * (j / Q) - (c + 1) * j := by
  have hcoef : 0 ≤ 1 - t := by linarith only [ht1]
  have hc_le : 1 - t ≤ 1 - c / z := by linarith only [hct]
  have hmain := mul_le_mul
    (mul_le_mul_of_nonneg_right hc_le hn)
    (div_le_div_of_nonneg_right hjlo hQ.le)
    (div_nonneg (mul_nonneg hcoef hn) hQ.le)
    (mul_nonneg (hcoef.trans hc_le) hn)
  have htwo : (1 - 2 * t) * n ^ 2 / Q ≤
      (1 - t) * n * (((1 - t) * n) / Q) := by
    have hs : 1 - 2 * t ≤ (1 - t) ^ 2 := by nlinarith only [sq_nonneg t]
    have hm := mul_le_mul_of_nonneg_right hs (div_nonneg (sq_nonneg n) hQ.le)
    convert hm using 1 <;> ring
  have hcost := mul_le_mul_of_nonneg_left hjhi (by linarith only [hc] : 0 ≤ c + 1)
  linarith only [htwo, hmain, hcost]

theorem with_errors {n j c z Q t e₁ e₂ : ℝ} (hn : 0 ≤ n) (hQ : 0 < Q)
    (ht1 : t ≤ 1) (hc : 0 ≤ c) (hct : c / z ≤ t)
    (hjlo : (1 - t) * n ≤ j) (hjhi : j ≤ n)
    (he : (c + 1) * n + e₁ + e₂ ≤ t * (n ^ 2 / Q)) :
    (1 - 3 * t) * (n ^ 2 / Q) ≤
      (1 - c / z) * n * (j / Q) - (c + 1) * j - e₁ - e₂ := by
  have hm := main_lower hn hQ ht1 hc hct hjlo hjhi
  have hid : (1 - 2 * t) * n ^ 2 / Q = (1 - 2 * t) * (n ^ 2 / Q) := by ring
  rw [hid] at hm
  nlinarith only [hm, he]

end PaperP1.AnchoredCostNormalization
