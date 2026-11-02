module

public import PaperP1.Analysis.ElementaryLogGrowth
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Exact pair-rank mass and conversion from a critical binary window to powers of N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalRankMass

theorem succ_coefficient_eventually (α ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, α * ((L + 1 : ℕ) : ℝ) ≤ (α + ε) * (L : ℝ) := by
  obtain ⟨L₀, hL₀⟩ := exists_nat_ge (α / ε)
  refine ⟨L₀, ?_⟩
  intro L hL
  have h : α / ε ≤ (L : ℝ) := hL₀.trans (by exact_mod_cast hL)
  have hm := (div_le_iff₀ hε).mp h
  push_cast
  nlinarith only [hm]

def rankMass (L d : ℕ) : ℝ := 4 * ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ d : ℝ)

theorem rankMass_exp (L d : ℕ) :
    rankMass L d = Real.exp (Real.log 4 + ((d : ℝ) - 2 * L) * Real.log 2) := by
  have hlog2 : Real.exp (Real.log (2 : ℝ)) = 2 := Real.exp_log (by norm_num)
  have hden : Real.exp (2 * (L : ℝ) * Real.log 2) = (2 ^ L : ℝ) ^ 2 := by
    calc
      _ = Real.exp ((2 : ℕ) * ((L : ℝ) * Real.log 2)) := by congr 1; push_cast; ring
      _ = Real.exp ((L : ℝ) * Real.log 2) ^ 2 := Real.exp_nat_mul _ 2
      _ = _ := by rw [Real.exp_nat_mul, hlog2]
  rw [sub_mul, Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4),
    Real.exp_nat_mul, hlog2, hden]
  unfold rankMass
  ring

theorem critical_rankMass_coefficient_bound (C a ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L d : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (d : ℝ) ≤ (a + ε / 2) * (L : ℝ) →
        rankMass L d ≤ (N : ℝ) ^ (a - 2 + ε) := by
  let β : ℝ := a - 2 + ε / 2
  let K : ℝ := Real.log 4 + |β| * |C| * Real.log 2
  obtain ⟨N₀, hN₀⟩ := ElementaryLogGrowth.log_ge_eventually (K / (ε / 2))
  refine ⟨N₀, ?_⟩
  intro N hN L d hband hrank
  obtain ⟨hlogN, hNtwo⟩ := hN₀ N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK : K ≤ (ε / 2) * Real.log N := by
    have h := (div_le_iff₀ (show (0 : ℝ) < ε / 2 by positivity)).mp hlogN
    linarith
  have herr : |(L : ℝ) * Real.log 2 - Real.log N| ≤ |C| * Real.log 2 := by
    have heq : (L : ℝ) * Real.log 2 - Real.log N =
        ((L : ℝ) - Real.log N / Real.log 2) * Real.log 2 := by
      field_simp
    rw [heq, abs_mul, abs_of_pos hlog2]
    exact mul_le_mul_of_nonneg_right (hband.trans (le_abs_self C)) hlog2.le
  have hβerr : β * ((L : ℝ) * Real.log 2 - Real.log N) ≤ |β| * |C| * Real.log 2 := by
    calc
      _ ≤ |β * ((L : ℝ) * Real.log 2 - Real.log N)| := le_abs_self _
      _ = |β| * |(L : ℝ) * Real.log 2 - Real.log N| := abs_mul _ _
      _ ≤ |β| * (|C| * Real.log 2) := mul_le_mul_of_nonneg_left herr (abs_nonneg β)
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_right hrank hlog2.le
  rw [rankMass_exp, Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  dsimp [β, K] at hβerr hK
  nlinarith only [hscaled, hβerr, hK]

theorem critical_rankMass_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L d : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (d : ℝ) ≤ (1 / 2 + ε / 2) * (L : ℝ) →
        rankMass L d ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  simpa only [show (1 / 2 : ℝ) - 2 + ε = -3 / 2 + ε by ring] using
    critical_rankMass_coefficient_bound C (1 / 2) ε hε

end PaperP1.CriticalRankMass
