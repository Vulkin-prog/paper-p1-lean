module

public import PaperP1.Asymptotics.FixedHeightQuadraticLaw

/-! # Both literal original-law equivalents and the height-five error of main Corollary 18.3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoChannelReference

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent
  PaperP1.HeightFiveChannelCorrection

theorem height_five_phase (N L : ℕ) :
    AdjacentReferencePhase.leadingGap N L 4 / 2 =
      17 * ((L % 5 : ℕ) + (4 : ℝ)) / (1200 * (2 : ℝ) ^ (((L % 5 : ℕ) : ℝ) / 5)) *
        (nominalMean N L) ^ (9 / 5 : ℝ) * PoissonDifferenceSigned.norm (nominalMean N L) 2 *
          L * (N : ℝ) ^ (-4 / 5 : ℝ) := by
  unfold AdjacentReferencePhase.leadingGap phaseMass
  rw [show 4 + 1 = (5 : ℕ) by decide, ChannelPhaseConstants.phaseConstant_five]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) - 1 / 5 = 9 / 5 by ring, show (-1 : ℝ) + 1 / 5 = -4 / 5 by ring]
  ring

theorem height_six_phase (N L : ℕ) :
    phaseMass N L 6 = (((L % 6 : ℕ) : ℝ) + 5) / (45 * (2 : ℝ) ^ (((L % 6 : ℕ) : ℝ) / 6)) *
      (nominalMean N L) ^ (11 / 6 : ℝ) * L * (N : ℝ) ^ (-5 / 6 : ℝ) := by
  rw [phaseMass, ChannelPhaseConstants.phaseConstant_six]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) - 1 / 6 = 11 / 6 by ring, show (-1 : ℝ) + 1 / 6 = -5 / 6 by ring]

theorem uniform_law_remainder (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SignedAtomicDistance.distance
        ((RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure -
          QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L))
        ((correction N L / 2) • QuadraticPoisson.differenceMap
          (QuadraticPoisson.differenceMap (QuadraticPoisson.poissonSigned (nominalMean N L)))) ≤
        (N : ℝ) ^ (-5 / 6 + ε) := by
  obtain ⟨N₀, hN₀, hh⟩ := FixedHeightQuadraticLaw.uniform_next_remainder 4 (by decide) C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have h := hh N hN L hband
  rw [coefficient_four N L (by omega)] at h
  simpa only [correction, heightMass, Nat.reduceAdd, Nat.cast_ofNat, show (-1 : ℝ) + 1 / 6 = -5 / 6 by ring] using h

theorem uniform_equivalents (C : ℝ) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ Q₄ Q₅ : ProbabilityMeasure ℕ,
        (Q₄ : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L) ∧
        (Q₅ : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference (nominalMean N L) (twoChannelCoefficient N L + correction N L) ∧
        0 < AdjacentReferencePhase.leadingGap N L 4 ∧
        0 < AdjacentReferencePhase.leadingGap N L 5 ∧
        |AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) Q₄ /
          (17 * (((L % 5 : ℕ) : ℝ) + 4) / (1200 * (2 : ℝ) ^ (((L % 5 : ℕ) : ℝ) / 5)) *
            (nominalMean N L) ^ (9 / 5 : ℝ) * PoissonDifferenceSigned.norm (nominalMean N L) 2 *
              L * (N : ℝ) ^ (-4 / 5 : ℝ)) - 1| ≤ τ ∧
        |AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) Q₅ /
          (phaseMass N L 6 * PoissonDifferenceSigned.norm (nominalMean N L) 2 / 4) - 1| ≤ τ := by
  have h₄ := FixedHeightQuadraticLaw.uniform_probability_equivalent 4 (by decide) C
  have h₅ := FixedHeightQuadraticLaw.uniform_probability_equivalent 5 (by decide) C
  intro τ hτ
  obtain ⟨N₄, _hN₄, h₄⟩ := h₄ τ hτ
  obtain ⟨N₅, _hN₅, h₅⟩ := h₅ τ hτ
  refine ⟨max 2 (max N₄ N₅), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨Q₄, hQ₄, hp₄, he₄⟩ := h₄ N (by omega) L hband
  obtain ⟨Q₅, hQ₅, hp₅, he₅⟩ := h₅ N (by omega) L hband
  rw [coefficient_four N L (by omega)] at hQ₄
  rw [coefficient_five, coefficient_four N L (by omega)] at hQ₅
  rw [height_five_phase] at he₄
  have hdenom : AdjacentReferencePhase.leadingGap N L 5 / 2 =
      phaseMass N L 6 * PoissonDifferenceSigned.norm (nominalMean N L) 2 / 4 := by
    unfold AdjacentReferencePhase.leadingGap
    ring
  rw [hdenom] at he₅
  exact ⟨Q₄, Q₅, hQ₄, hQ₅, hp₄, hp₅, he₄, he₅⟩

end PaperP1.TwoChannelReference
