module

public import PaperP1.Arithmetic.DegreeUniformAffineParameters
public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Exact critical-band and subpower control of the binary logarithmic budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryLogarithmicBudget

open DegreeUniformAffineParameters CriticalBandScale

theorem critical_band (N : ℕ) (hN : 1 ≤ N) :
    |(logarithmicBudget N : ℝ) - Real.log N / Real.log 2| ≤ 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (2 : ℝ) ^ Nat.log2 N ≤ N := by
    exact_mod_cast (by simpa only [Nat.log2_eq_log_two] using
      Nat.pow_log_le_self 2 (show N ≠ 0 by omega))
  have hhi : (N : ℝ) ≤ (2 : ℝ) ^ logarithmicBudget N := by exact_mod_cast (binary_upper N).le
  have hloglo := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 N) hlo
  have hloghi := Real.log_le_log hNp hhi
  rw [Real.log_pow] at hloglo hloghi
  have hrlo : (Nat.log2 N : ℝ) ≤ Real.log N / Real.log 2 := (le_div_iff₀ hlog).mpr hloglo
  have hrhi : Real.log N / Real.log 2 ≤ (logarithmicBudget N : ℝ) := (div_le_iff₀ hlog).mpr hloghi
  have hcast : (logarithmicBudget N : ℝ) = (Nat.log2 N : ℝ) + 1 := by simp only [logarithmicBudget, Nat.cast_add, Nat.cast_one]
  apply abs_le.mpr
  constructor <;> linarith only [hrlo, hrhi, hcast]

theorem polynomial_absorption (K : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      |K * (logarithmicBudget N : ℝ) ^ k| ≤ (N : ℝ) ^ ε := by
  obtain ⟨NG, hg⟩ := critical_band_scale 1
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le K k ε hε
  refine ⟨2 + NG + NP, by omega, ?_⟩
  intro N hN
  have hbound := (hg N (by omega) (logarithmicBudget N) (critical_band N (by omega))).2
  have hle : (logarithmicBudget N : ℝ) ≤ ((logarithmicBudget N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (logarithmicBudget N)
  have hbudget : (logarithmicBudget N : ℝ) ≤ upperScale * Real.log N := hle.trans hbound
  have hh := hp N (by omega) (Nat.log2 N) hbudget
  simpa only [logarithmicBudget, Nat.cast_add, Nat.cast_one] using hh

end PaperP1.BinaryLogarithmicBudget
