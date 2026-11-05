module

public import PaperP1.Asymptotics.LeadingSignedCostTheorem
public import PaperP1.Asymptotics.StratifiedSignedCostUpper
public import PaperP1.Analysis.LeadingSaddleLogBounds

/-! # The original specified signed cost has leading logarithmic coefficient two

All bounds are uniform on the literal original critical band. The sequence
limit retains any actual critical choice of lengths and the prescribed excess.
The fine o(nu_N) error is not asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LeadingSignedCostBounds

open Filter SaddleParameters SaddleScales HardSaddleGrowth SignedSaddleCostTheorem
  LeadingSaddleLogBounds

theorem uniform_sandwich (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Real.exp (-(2 + ε) * saddleCutoff 1 (Real.log N)) ≤ specifiedCost N L ∧
          specifiedCost N L ≤ Real.exp (-(2 - ε) * saddleCutoff 1 (Real.log N)) := by
  obtain ⟨NL, hl⟩ := LeadingSignedCostTheorem.uniform_lower C (2 + ε) (by linarith only [hε])
  obtain ⟨NU, hu⟩ := StratifiedSignedCostUpper.uniform_upper C (2 - ε) (by linarith only [hε])
  exact ⟨max NL NU, fun N hN L hL hcrit ↦
    ⟨hl N (by omega) L hL hcrit, hu N (by omega) L hL hcrit⟩⟩

theorem uniform_normalized_bounds (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        2 - ε ≤ -Real.log (specifiedCost N L) / saddleCutoff 1 (Real.log N) ∧
          -Real.log (specifiedCost N L) / saddleCutoff 1 (Real.log N) ≤ 2 + ε := by
  obtain ⟨NC, hc⟩ := uniform_sandwich C ε hε
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop HB))
  refine ⟨max NC NG, ?_⟩
  intro N hN L hL hcrit
  have hV := (hb (Real.log N) (hg N (by omega))).2.1
  obtain ⟨hl, hu⟩ := hc N (by omega) L hL hcrit
  exact cost_log_bounds hV hl hu

theorem uniform_logarithmic_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |Real.log (specifiedCost N L) + 2 * saddleCutoff 1 (Real.log N)| ≤
          ε * saddleCutoff 1 (Real.log N) := by
  obtain ⟨N₀, h⟩ := uniform_sandwich C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL hcrit
  obtain ⟨hl, hu⟩ := h N hN L hL hcrit
  have hs : 0 < specifiedCost N L := (Real.exp_pos _).trans_le hl
  have hlow := Real.log_le_log (Real.exp_pos _) hl
  have hhigh := Real.log_le_log hs hu
  rw [Real.log_exp] at hlow hhigh
  rw [abs_le]
  constructor <;> nlinarith only [hlow, hhigh]

theorem normalized_limit (C : ℝ) (L : ℕ → ℕ)
    (hcrit : ∀ᶠ N : ℕ in atTop, 1 ≤ L N ∧ |(L N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Tendsto (fun N : ℕ ↦ -Real.log (specifiedCost N (L N)) / saddleCutoff 1 (Real.log N))
      atTop (nhds 2) := by
  obtain ⟨NC, hc⟩ := eventually_atTop.mp hcrit
  apply limit_of_uniform_bounds
  intro ε hε
  obtain ⟨N₀, h⟩ := uniform_normalized_bounds C ε hε
  refine ⟨max (max N₀ 2) NC, ?_⟩
  intro N hN
  obtain ⟨hL, hcritical⟩ := hc N (by omega)
  exact h N (by omega) (L N) hL hcritical

end PaperP1.LeadingSignedCostBounds
