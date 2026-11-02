module

public import PaperP1.Model.DirectPairProductComparison
public import PaperP1.Asymptotics.OverlappingPairProductCostUnderBCN

/-! # Source-scale pair-product reduction to the literal disjoint non-direct cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectPairProductReductionUnderBCN

open Finset PaperP1.Model PaperP1.DirectPairProductComparison

theorem uniform_reduction (c κ : ℝ) (hc : 0 < c)
    (hBCN : PlaneCurvePointCount.UniformBound c κ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2 / 2 - signedDirect G L| ≤
        nonDirectApartCost G L + (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := OverlappingPairProductCostUnderBCN.uniform_repeated_square c κ hc hBCN C ε hε
  obtain ⟨NS, _hNS, hs⟩ := OverlappingPairProductCostUnderBCN.uniform_star_square c κ hc hBCN C ε hε
  refine ⟨max 2 (max NR NS), by omega, ?_⟩
  intro N hN L hband G hG
  have hfinite := finite_bound G L
  have hrepeat := hr N (by omega) L hband G hG
  have hstar := hs N (by omega) L hband G hG
  linarith only [hfinite, hrepeat, hstar]

end PaperP1.DirectPairProductReductionUnderBCN
