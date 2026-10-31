module

public import PaperP1.Asymptotics.ExpSqrtLog

@[expose] public section

/-! # Elementary explicit logarithmic growth estimates -/

namespace PaperP1.ElementaryLogGrowth

theorem log_le_two_sqrt {s : ℝ} (hs : 0 < s) :
    Real.log s ≤ 2 * Real.sqrt s := by
  have h := Real.log_le_log hs (ExpSqrtLog.le_exp_two_mul_sqrt hs.le)
  simpa only [Real.log_exp] using h

theorem thirtyTwo_mul_log_le {s : ℝ} (hs : 4096 ≤ s) :
    32 * Real.log s ≤ s := by
  have hs0 : 0 ≤ s := by linarith
  have hroot : (64 : ℝ) ≤ Real.sqrt s :=
    (Real.le_sqrt (by norm_num) hs0).mpr
      (by simpa only [show (64 : ℝ) ^ 2 = 4096 by norm_num] using hs)
  have hlog := log_le_two_sqrt (show 0 < s by linarith)
  have hsq := Real.sq_sqrt hs0
  have hprod : 0 ≤ (Real.sqrt s - 64) * Real.sqrt s :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg s)
  nlinarith

theorem square_le_four_mul_exp {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 ≤ 4 * Real.exp s := by
  have hhalf : s / 2 ≤ Real.exp (s / 2) := by
    linarith [Real.add_one_le_exp (s / 2)]
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ s / 2) hhalf 2
  have hexp : (Real.exp (s / 2)) ^ 2 = Real.exp s := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hsq
  nlinarith

/-- Every fixed lower logarithmic threshold holds eventually, with N ≥ 2. -/
theorem log_ge_eventually (S : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, S ≤ Real.log (N : ℝ) ∧ 2 ≤ N := by
  obtain ⟨Ncore, hNcore⟩ := exists_nat_gt (Real.exp S)
  refine ⟨max Ncore 2, ?_⟩
  intro N hN
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hexp : Real.exp S < (N : ℝ) :=
    hNcore.trans_le (by exact_mod_cast (le_max_left Ncore 2).trans hN)
  have hlog := Real.log_lt_log (Real.exp_pos S) hexp
  exact ⟨by simpa only [Real.log_exp] using hlog.le, hNtwo⟩

end PaperP1.ElementaryLogGrowth

