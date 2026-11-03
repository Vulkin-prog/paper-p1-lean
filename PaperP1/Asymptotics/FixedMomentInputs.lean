module

public import PaperP1.Asymptotics.FixedQuadraticFactorialMomentsUnderInputs

/-! # A finite bundle of precisely the existing geometric properties for the completed fixed factorial correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedMomentInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.HeterogeneousDirectMaximum

structure Parameters (r : ℕ) where
  compatible : CoarseConnectedParameters.Parameters r
  incompatible : CoarseConnectedParameters.Parameters r
  nonconnected : CoarseConnectedParameters.Parameters r
  pair : FinitePairDeficitInputs.Parameters
  nonconnectedPair : FinitePairDeficitInputs.Parameters

structure Hypotheses {r : ℕ} (p : Parameters r) (ε : ℝ) : Prop where
  compatible : CoarseConnectedParameters.Hypotheses p.compatible (ε / 128)
  incompatible : CoarseConnectedParameters.Hypotheses p.incompatible (ε / 512)
  pair : FinitePairDeficitInputs.Hypotheses p.pair (GeneralGraphHostCount.sizeCap (ε / 524288))
  nonconnected : CoarseConnectedParameters.Hypotheses p.nonconnected (min (ε / 32) (1 / 12) / 8)
  nonconnectedPair : FinitePairDeficitInputs.Hypotheses p.nonconnectedPair
    (GeneralGraphHostCount.sizeCap (min (ε / 32) (1 / 12) / 8192))

theorem uniform_fixed (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters r, Hypotheses p ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      |factorialCountMoment G L r - actualMean G L ^ r -
        (r.choose 2 : ℝ) * actualMean G L ^ (r - 2) * RegularCumulantTransfer.secondFactorialCumulant G L| ≤
          (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨pc, pi, pd, pp, pq, h⟩ := FixedQuadraticFactorialMomentsUnderInputs.uniform_fixed r hr C ε hε
  refine ⟨⟨pc, pi, pd, pp, pq⟩, ?_⟩
  intro hp
  exact h hp.compatible hp.incompatible hp.pair hp.nonconnected hp.nonconnectedPair

end PaperP1.FixedMomentInputs
