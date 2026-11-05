module

public import PaperP1.Asymptotics.PairActivity
public import PaperP1.Asymptotics.CriticalActualMean
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Unconditional smallness and mean separation of the actual second cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondCumulant

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤ (N : ℝ) ^ (-2 / 3 + ε) :=
  PairActivity.uniform_cumulant C ε hε

theorem uniform_eventually_small (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |RegularCumulantTransfer.secondFactorialCumulant G L| ≤ δ := by
  obtain ⟨NA, hNA, hbound⟩ := uniform_bound C (5 / 12) (by norm_num)
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨NT, htail⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hδ))
  refine ⟨max NA NT, by omega, ?_⟩
  intro N hN L hband G hG
  have h := hbound N (by omega) L hband G hG
  norm_num only [show -(2 : ℝ) / 3 + 5 / 12 = -(1 / 4) by ring] at h
  exact h.trans (htail N (by omega)).le

theorem uniform_parameter_gap (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L| ≤
          countMoment (dyadicBlock N) L 1 / 2 ∧
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L <
          countMoment (dyadicBlock N) L 1 := by
  have hmean : 0 < CriticalActualMean.lowerMean C := CriticalActualMean.lowerMean_pos C
  obtain ⟨NA, hNA, hsmall⟩ := uniform_eventually_small C
    (CriticalActualMean.lowerMean C / 4) (by positivity)
  obtain ⟨NM, hNM, hmeanbound⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨max NA NM, by omega, ?_⟩
  intro N hN L hband
  have ha := hsmall N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hm := (hmeanbound N (by omega) L hband).1
  have hh := le_abs_self (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)
  constructor <;> linarith only [hmean, ha, hm, hh]

end PaperP1.SecondCumulant
