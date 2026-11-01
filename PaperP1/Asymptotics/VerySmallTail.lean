module

public import PaperP1.Asymptotics.NearLinearThreshold

/-! # Actual very small tails and moments through logarithmic order

The growing-order factorial bound is proved before Markov is applied.
All probabilities and truncated moments are those of the infinite prime-sign law.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VerySmallTail

open PaperP1.Model

theorem moment_bound {N L : ℕ} {b : ℝ} (hn : 0 < (N : ℝ)) (hH : 1 ≤ Real.log N)
    (hprob : CountTailBounds.probability N L b ≤ Real.exp (-2 * (Real.log N) ^ 3))
    (r : ℕ) (hr : (r : ℝ) ≤ Real.log N) :
    CountTailBounds.moment N L b r ≤ Real.exp (-(Real.log N) ^ 3 / 2) := by
  have hNr : (N : ℝ) ^ r = Real.exp (Real.log N * (r : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hn]
  have hrH := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ Real.log N)
  have hcubic := mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg (Real.log N))
  calc
    _ ≤ (N : ℝ) ^ r * CountTailBounds.probability N L b :=
      CountTailBounds.moment_le_count_power N L b r
    _ ≤ (N : ℝ) ^ r * Real.exp (-2 * (Real.log N) ^ 3) :=
      mul_le_mul_of_nonneg_left hprob (by positivity)
    _ = Real.exp (Real.log N * (r : ℝ) - 2 * (Real.log N) ^ 3) := by
      rw [hNr, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(Real.log N) ^ 3 / 2) := Real.exp_le_exp.mpr (by nlinarith)

theorem power_threshold (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ b : ℝ,
      QuadraticTailScale.threshold N ≤ b →
      CountTailBounds.probability N L b ≤ Real.exp (-2 * (Real.log N) ^ 3) ∧
        ∀ r : ℕ, (r : ℝ) ≤ Real.log N →
          CountTailBounds.moment N L b r ≤ Real.exp (-(Real.log N) ^ 3 / 2) := by
  obtain ⟨Nprob, hNprob, hprob⟩ := QuadraticTailScale.probability_bound C
  obtain ⟨Nscale, _, hscale⟩ := QuadraticTailScale.scales_eventually
  refine ⟨max Nprob Nscale, by omega, ?_⟩
  intro N hN L hband b hb
  have hp := (CountTailBounds.probability_mono hb).trans (hprob N (by omega) L hband)
  refine ⟨hp, ?_⟩
  intro r hr
  exact moment_bound (by exact_mod_cast (show 0 < N by omega))
    (hscale N (by omega)).1 hp r hr

/-- The source proposition, with the improved range of every fixed c > 0. -/
theorem companion_T19_6 (C c : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CountTailBounds.probability N L (NearLinearThreshold.threshold N L c : ℝ) ≤
          Real.exp (-(Real.log N) ^ 3) ∧
        ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ Real.log N →
          CountTailBounds.moment N L (NearLinearThreshold.threshold N L c : ℝ) r ≤
            Real.exp (-(Real.log N) ^ 3 / 2) := by
  obtain ⟨Npower, hNpower, hpower⟩ := power_threshold C
  obtain ⟨Nnear, _, hnear⟩ := NearLinearThreshold.threshold_ge_power C c hc
  refine ⟨max Npower Nnear, by omega, ?_⟩
  intro N hN L hband
  obtain ⟨hp, hm⟩ := hpower N (by omega) L hband _ (hnear N (by omega) L hband)
  have hH : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  refine ⟨hp.trans (Real.exp_le_exp.mpr (by nlinarith [pow_nonneg hH 3])), ?_⟩
  intro r _ hr
  exact hm r hr

end PaperP1.VerySmallTail
