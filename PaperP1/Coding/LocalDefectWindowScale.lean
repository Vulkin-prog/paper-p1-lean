module

public import PaperP1.Coding.LocalDefectAsymptotic

@[expose] public section

/-! # The local O(B/log B) conclusion of companion T1.3 -/

namespace PaperP1.LocalDefectWindowScale

open LocalDefectBound

/-- Fixed comparison constants are chosen before the common constant and
threshold. The cutoff and interval width need only upper bounds by B. -/
theorem local_defect_count_le_window_scale_eventually
    (c C b Bmax Hscale Rscale : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hb : 0 < b) (hBmax : 0 ≤ Bmax)
    (hHscale : 0 ≤ Hscale) (hRscale : 0 ≤ Rscale) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℝ, ∀ H U R : ℕ,
      b * Real.log N ≤ B → B ≤ Bmax * Real.log N →
      (H : ℝ) ≤ Hscale * B → (R : ℝ) ≤ Rscale * B →
      c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
      ((defectsInInterval H U R).card : ℝ) ≤ K * B / Real.log B := by
  obtain ⟨Kcore, hKcore, Ncore, hcore⟩ :=
    LocalDefectAsymptotic.local_defect_count_le_log_div_loglog_eventually
      c C (Hscale * Bmax) (Rscale * Bmax) hc hC
      (mul_nonneg hHscale hBmax) (mul_nonneg hRscale hBmax)
  obtain ⟨Nlog, hNlog⟩ :=
    ElementaryLogGrowth.log_ge_eventually (4 + 2 / b + Bmax)
  refine ⟨Kcore * (2 / b), by positivity, max Ncore Nlog, ?_⟩
  intro N hN B H U R hBlo hBhi hH hR hUlo hUhi
  let s : ℝ := Real.log N
  have hs : 4 + 2 / b + Bmax ≤ s := (hNlog N ((le_max_right _ _).trans hN)).1
  have hdiv0 : 0 ≤ 2 / b := by positivity
  have hs4 : 4 ≤ s := by linarith
  have hspos : 0 < s := by linarith
  have hs0 : 0 ≤ s := hspos.le
  have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
  have hBmaxs : Bmax ≤ s := by linarith
  have htwodiv : 2 / b ≤ s := by linarith
  have hbs : 2 ≤ b * s := by
    have h := (div_le_iff₀ hb).mp htwodiv
    nlinarith
  have hBtwo : 2 ≤ B := hbs.trans hBlo
  have hBpos : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hBsquare : B ≤ s ^ 2 := by
    calc
      B ≤ Bmax * s := hBhi
      _ ≤ s * s := mul_le_mul_of_nonneg_right hBmaxs hs0
      _ = s ^ 2 := by ring
  have hlogBupper : Real.log B ≤ 2 * Real.log s := by
    have h := Real.log_le_log hBpos hBsquare
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hBscaled : 2 * s ≤ (2 / b) * B := by
    calc
      2 * s = (2 / b) * (b * s) := by field_simp
      _ ≤ (2 / b) * B := mul_le_mul_of_nonneg_left hBlo (by positivity)
  have hratio : s / Real.log s ≤ ((2 / b) * B) / Real.log B := by
    apply (div_le_div_iff₀ hlogs hlogB).mpr
    calc
      s * Real.log B ≤ s * (2 * Real.log s) :=
        mul_le_mul_of_nonneg_left hlogBupper hs0
      _ = (2 * s) * Real.log s := by ring
      _ ≤ ((2 / b) * B) * Real.log s :=
        mul_le_mul_of_nonneg_right hBscaled hlogs.le
  have hHlog : (H : ℝ) ≤ (Hscale * Bmax) * Real.log N := by
    calc
      _ ≤ Hscale * B := hH
      _ ≤ Hscale * (Bmax * Real.log N) :=
        mul_le_mul_of_nonneg_left hBhi hHscale
      _ = _ := by ring
  have hRlog : (R : ℝ) ≤ (Rscale * Bmax) * Real.log N := by
    calc
      _ ≤ Rscale * B := hR
      _ ≤ Rscale * (Bmax * Real.log N) :=
        mul_le_mul_of_nonneg_left hBhi hRscale
      _ = _ := by ring
  have hcount := hcore N ((le_max_left _ _).trans hN) H U R hHlog hRlog hUlo hUhi
  calc
    _ ≤ Kcore * s / Real.log s := hcount
    _ = Kcore * (s / Real.log s) := by ring
    _ ≤ Kcore * (((2 / b) * B) / Real.log B) :=
      mul_le_mul_of_nonneg_left hratio hKcore.le
    _ = (Kcore * (2 / b)) * B / Real.log B := by ring

end PaperP1.LocalDefectWindowScale

