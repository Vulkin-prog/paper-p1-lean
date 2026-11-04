module

public import PaperP1.Analysis.ReducedSourceBarrier

/-! # Transfer both the reduced shift and source-barrier loss to the effective logarithm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedSourceShiftBudget

open PaperP1.ReducedSourceParameter PaperP1.ReducedSourceBarrier

theorem polylog_rebase (K A t t' H : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (ht : 0 ≤ t) (ht' : 0 ≤ t')
    (hcompare : t ≤ 2 * t') (hH : H ≤ K * t ^ A) : H ≤ (K * (2 : ℝ) ^ A) * t' ^ A := by
  calc
    _ ≤ K * t ^ A := hH
    _ ≤ K * (2 * t') ^ A := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht hcompare hA) hK
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht']; ring

theorem shift_and_loss_bounds (N g q h : ℕ) (hN : 0 < N) (hg : 0 < g) (hq : 0 < q)
    (hscale : g ^ 2 * q ≤ h) (hroot : (h : ℝ) ≤ Real.sqrt N) (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hshift : (h : ℝ) ≤ K * (Real.log N) ^ A) :
    0 < h / (g ^ 2 * q) ∧
      ((h / (g ^ 2 * q) : ℕ) : ℝ) ≤ (K * (2 : ℝ) ^ A) * (Real.log (parameter N (g ^ 2 * q))) ^ A ∧
      0 ≤ loss g q ∧ loss g q ≤ (2 * K * (2 : ℝ) ^ A) * (Real.log (parameter N (g ^ 2 * q))) ^ A := by
  have hs : 0 < g ^ 2 * q := Nat.mul_pos (pow_pos hg 2) hq
  have hp := parameter_positive N (g ^ 2 * q) hN hs
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogP : 0 ≤ Real.log (parameter N (g ^ 2 * q)) := Real.log_nonneg (by exact_mod_cast hp)
  have hlogLower := parameter_log_lower N (g ^ 2 * q) h hN hs hscale hroot
  have hparent := polylog_rebase K A (Real.log N) (Real.log (parameter N (g ^ 2 * q))) h hK hA hlogN hlogP
    (by linarith) hshift
  have hdiv : ((h / (g ^ 2 * q) : ℕ) : ℝ) ≤ h := by exact_mod_cast Nat.div_le_self h (g ^ 2 * q)
  have htwice := mul_le_mul_of_nonneg_left hparent (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨Nat.div_pos hscale hs, hdiv.trans hparent, loss_nonnegative g q,
    by simpa only [mul_assoc] using (loss_le_twice_shift g q h hq hscale).trans htwice⟩

end PaperP1.ReducedSourceShiftBudget
