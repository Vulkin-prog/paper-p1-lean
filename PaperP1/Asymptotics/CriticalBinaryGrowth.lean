module

public import PaperP1.Asymptotics.HalfCountSchedule
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Uniform growth of a binary rank cap in the critical band -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalBinaryGrowth

def constant (C θ : ℝ) : ℝ := Real.exp (|θ| * |C| * Real.log 2)

theorem upper {N L k : ℕ} {C θ : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (hk : (k : ℝ) ≤ θ * L) :
    (2 ^ k : ℝ) ≤ constant C θ * (N : ℝ) ^ θ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have herr : |(L : ℝ) * Real.log 2 - Real.log N| ≤ |C| * Real.log 2 := by
    have heq : (L : ℝ) * Real.log 2 - Real.log N =
        ((L : ℝ) - Real.log N / Real.log 2) * Real.log 2 := by field_simp
    rw [heq, abs_mul, abs_of_pos hlogtwo]
    exact mul_le_mul_of_nonneg_right (hband.trans (le_abs_self C)) hlogtwo.le
  have hθ : θ * ((L : ℝ) * Real.log 2 - Real.log N) ≤ |θ| * |C| * Real.log 2 := by
    calc
      _ ≤ |θ * ((L : ℝ) * Real.log 2 - Real.log N)| := le_abs_self _
      _ = |θ| * |(L : ℝ) * Real.log 2 - Real.log N| := abs_mul _ _
      _ ≤ |θ| * (|C| * Real.log 2) := mul_le_mul_of_nonneg_left herr (abs_nonneg θ)
      _ = _ := by ring
  have hscale := mul_le_mul_of_nonneg_right hk hlogtwo.le
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    constant, Real.rpow_def_of_pos hn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hθ, hscale]

theorem uniform_upper (C θ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L k : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (k : ℝ) ≤ θ * L →
      (2 ^ k : ℝ) ≤ (N : ℝ) ^ (θ + ε) := by
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (constant C θ) θ ε hε
  refine ⟨max 2 NA, by omega, ?_⟩
  intro N hN L k hband hk
  exact (upper (by omega) hband hk).trans (ha N (by omega))

end PaperP1.CriticalBinaryGrowth
