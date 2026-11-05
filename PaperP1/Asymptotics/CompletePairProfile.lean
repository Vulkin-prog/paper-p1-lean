module

public import PaperP1.Asymptotics.PositiveSeparatedSourceProfile
public import PaperP1.Asymptotics.SignedSeparatedSourceProfile
public import PaperP1.Asymptotics.ActualPairPhase

/-! # The complete unconditional original-model pair profile

The phase masses have the literal moving residue-class formulas established by
PrincipalPairPhaseComparison.phase_three and phase_four. The whole first channel
is subtracted before the second equivalent is taken.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletePairProfile

open Finset PaperP1.Model PaperP1.PrincipalPairPhaseComparison
  PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent

theorem main_3_3 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L,
          ((2 ^ NormalizedPairRankLoss.pairLoss p.1 p.2 L : ℝ) - 1)) -
          PositiveSeparatedSourceProfile.mainTerm N L| ≤ (N : ℝ) ^ (6 / 5 + ε) ∧
      |(∑ p ∈ PairSeparation.separatedHosts (dyadicBlock N) L,
          SourcePairAffineWeight.signedWeight p.1 p.2 L) -
          SignedSourceProfile.mainTerm N L| ≤ (N : ℝ) ^ (6 / 5 + ε) ∧
      |ActualPairPhase.alpha N L - (nominalMean N L) ^ 2 / (3 * N) *
          ((ChannelSumIdentity.signed L 2 3 : ℤ) + (ChannelSumIdentity.signed L 3 4 : ℤ))| ≤
          (N : ℝ) ^ (-4 / 5 + ε) ∧
      (0 < phaseMass N L 3 ∧ 0 < phaseMass N L 4 ∧
        |ActualPairPhase.alpha N L / phaseMass N L 3 - 1| ≤ ε ∧
        |(ActualPairPhase.alpha N L - ChannelMainTermBounds.mainTerm N L 2 3) /
          phaseMass N L 4 - 1| ≤ ε) := by
  obtain ⟨NP, _hNP, hp⟩ := PositiveSeparatedSourceProfile.article_3_3_positive C ε hε
  obtain ⟨NS, _hNS, hs⟩ := SignedSeparatedSourceProfile.article_3_3_signed C ε hε
  obtain ⟨NC, _hNC, hc⟩ := ActualPairPhase.article_3_3_cumulant C ε hε
  obtain ⟨NF, _hNF, hf⟩ := ActualPairPhase.uniform_phases C ε hε
  refine ⟨2 + NP + NS + NC + NF, by omega, ?_⟩
  intro N hN L hband
  exact ⟨hp N (by omega) L hband, hs N (by omega) L hband,
    hc N (by omega) L hband, hf N (by omega) L hband⟩

end PaperP1.CompletePairProfile
