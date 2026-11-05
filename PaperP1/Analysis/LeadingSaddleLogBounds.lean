module

public import PaperP1.Analysis.HardSaddleGrowth

/-! # Finite logarithmic bounds and leading coefficient limits

Fixed margins around coefficient two suffice for a leading limit. They do not
supply a remainder smaller than the hard saddle.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LeadingSaddleLogBounds

open Filter

theorem reciprocal_log_bounds {N : ℕ} {S V A B : ℝ} (hN : 0 < N) (hV : 0 < V)
    (hl : (N : ℝ) * Real.exp (-A * V) ≤ S)
    (hu : S ≤ (N : ℝ) * Real.exp (-B * V)) :
    B ≤ (Real.log N - Real.log S) / V ∧ (Real.log N - Real.log S) / V ≤ A := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < S := (mul_pos hn (Real.exp_pos _)).trans_le hl
  have hlow := Real.log_le_log (mul_pos hn (Real.exp_pos _)) hl
  have hhigh := Real.log_le_log hs hu
  rw [Real.log_mul hn.ne' (Real.exp_ne_zero _), Real.log_exp] at hlow hhigh
  exact ⟨(le_div_iff₀ hV).mpr (by linarith only [hhigh]),
    (div_le_iff₀ hV).mpr (by linarith only [hlow])⟩

theorem cost_log_bounds {S V A B : ℝ} (hV : 0 < V)
    (hl : Real.exp (-A * V) ≤ S) (hu : S ≤ Real.exp (-B * V)) :
    B ≤ -Real.log S / V ∧ -Real.log S / V ≤ A := by
  have hs : 0 < S := (Real.exp_pos _).trans_le hl
  have hlow := Real.log_le_log (Real.exp_pos _) hl
  have hhigh := Real.log_le_log hs hu
  rw [Real.log_exp] at hlow hhigh
  exact ⟨(le_div_iff₀ hV).mpr (by linarith only [hhigh]),
    (div_le_iff₀ hV).mpr (by linarith only [hlow])⟩

theorem limit_of_uniform_bounds (F : ℕ → ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      2 - ε ≤ F N ∧ F N ≤ 2 + ε) : Tendsto F atTop (nhds 2) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N₀, h⟩ := hbound (ε / 2) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hl, hu⟩ := h N hN
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith only [hl, hu, hε]

end PaperP1.LeadingSaddleLogBounds
