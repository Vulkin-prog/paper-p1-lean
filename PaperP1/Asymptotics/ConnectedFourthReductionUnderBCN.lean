module

public import PaperP1.Model.ConnectedFourthReduction
public import PaperP1.Asymptotics.DirectPairProductReductionUnderBCN
public import PaperP1.Asymptotics.FourthRepeatedRunCostUnderBCN

/-! # Source precision for the fourth cumulant apart from one literal arithmetic cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedFourthReductionUnderBCN

open Finset PaperP1.Model PaperP1.FourthRunFactorialCumulant PaperP1.DirectPairProductComparison

theorem uniform_reduction (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |fourthFactorialCumulant G L -
        24 * CompatibleActivitySplit.signed L (ConnectedWindowFamilies.connectedFamilies G L 4)| ≤
        24 * nonDirectApartCost G L + (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NR, _hNR, hr⟩ := FourthRepeatedRunCostUnderBCN.uniform_bound c κ hc hBCN C η hη
  obtain ⟨NP, _hNP, hp⟩ := DirectPairProductReductionUnderBCN.uniform_reduction c κ hc hBCN C η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 25 (-3 / 2 + η) η hη
  refine ⟨max 2 (max NR (max NP (max NG NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hrem := hr N (by omega) L hband G hG
  have hpair := hp N (by omega) L hband G hG
  have ht := abs_sub (FourthRunRemainder.remainder G L)
    (24 * (CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2 / 2 - signedDirect G L))
  rw [abs_mul] at ht
  rw [show |(24 : ℝ)| = 24 by norm_num] at ht
  have hfactor : 25 * (N : ℝ) ^ (-3 / 2 + η) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    dsimp [η]
    ring
  rw [ConnectedFourthReduction.exact_reduction G L hL]
  linarith only [ht, hrem, hpair, hfactor]

end PaperP1.ConnectedFourthReductionUnderBCN
