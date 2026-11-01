module

public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Analysis.ElementaryLogGrowth

/-! # One uniform critical-window threshold for width and macroscopic separation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalWindowGeometry

open Filter PaperP1.CriticalBandScale

theorem uniform_geometry (C : ℝ) (Bmin : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 ≤ N ∧ Bmin ≤ L + 1 ∧ 2 ≤ L + 1 ∧ 8 * (L + 1) ≤ N ∧
        lowerScale * Real.log N ≤ ((L + 1 : ℕ) : ℝ) ∧
        ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N := by
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually (((max Bmin 2 : ℕ) : ℝ) / lowerScale)
  have hthin : ∀ᶠ N : ℕ in atTop, Real.log N / N < 1 / (8 * upperScale) :=
    (tendsto_order.1 PaperP1.PrimeLogBudget.log_nat_div_self_tendsto).2 _
      (div_pos zero_lt_one (mul_pos (by norm_num) upperScale_pos))
  obtain ⟨Nthin, hNthin⟩ := eventually_atTop.1 hthin
  refine ⟨max Nscale (max Nlog (max Nthin 2)), ?_⟩
  intro N hN L hcrit
  have hNtwo : 2 ≤ N := (le_max_right Nthin 2).trans ((le_max_right Nlog _).trans ((le_max_right _ _).trans hN))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hBlo, hBhi⟩ := hscale N ((le_max_left _ _).trans hN) L hcrit
  have hlogN := (hlog N ((le_max_left Nlog _).trans ((le_max_right _ _).trans hN))).1
  have hlarge : max Bmin 2 ≤ L + 1 := by
    have h := (div_le_iff₀ lowerScale_pos).mp hlogN
    have hB : ((max Bmin 2 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by nlinarith only [h, hBlo]
    exact_mod_cast hB
  have hwidth : 8 * (L + 1) ≤ N := by
    have h := (div_lt_div_iff₀ hNpos (mul_pos (by norm_num) upperScale_pos)).mp
      (hNthin N ((le_max_left Nthin 2).trans ((le_max_right Nlog _).trans ((le_max_right _ _).trans hN))))
    have hR : ((8 * (L + 1) : ℕ) : ℝ) ≤ N := by
      push_cast
      push_cast at hBhi
      nlinarith only [h, hBhi]
    exact_mod_cast hR
  exact ⟨hNtwo, (le_max_left _ _).trans hlarge, (le_max_right _ _).trans hlarge, hwidth, hBlo, hBhi⟩

end PaperP1.CriticalWindowGeometry
