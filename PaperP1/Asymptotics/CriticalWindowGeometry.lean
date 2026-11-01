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

theorem log_base_lower {N B U : ℕ} (hN : 4 ≤ N) (hNU : N ≤ 2 * U)
    (hB : (B : ℝ) ≤ upperScale * Real.log N) :
    (1 / (2 * upperScale)) * (B : ℝ) ≤ Real.log U := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhalf : (N : ℝ) / 2 ≤ U := by
    have h : (N : ℝ) ≤ 2 * U := by exact_mod_cast hNU
    linarith only [h]
  have hmono := Real.log_le_log (by positivity : 0 < (N : ℝ) / 2) hhalf
  rw [Real.log_div hNpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
  have hNfour : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogfour := Real.log_le_log (by norm_num : 0 < (2 : ℝ) ^ 2)
    (show (2 : ℝ) ^ 2 ≤ N by convert hNfour using 1; norm_num)
  rw [Real.log_pow] at hlogfour
  norm_num only [Nat.cast_ofNat] at hlogfour
  have hcoef : (1 / (2 * upperScale)) * (B : ℝ) ≤ Real.log N / 2 := by
    calc
      _ = (B : ℝ) / (2 * upperScale) := by ring
      _ ≤ Real.log N / 2 := (div_le_iff₀ (mul_pos (by norm_num) upperScale_pos)).mpr (by nlinarith only [hB])
  linarith only [hcoef, hmono, hlogfour]

end PaperP1.CriticalWindowGeometry
