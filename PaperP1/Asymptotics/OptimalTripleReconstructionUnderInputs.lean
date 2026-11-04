module

public import PaperP1.Asymptotics.PolynomialWeightedQuadraticUnderInputs

/-! # Both clauses of the article's triple-activity reconstruction theorem -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalTripleReconstructionUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.CountObservables

structure Parameters where
  symbolic : TripleActivityLawReconstructionUnderInputs.Parameters
  optimal : PolynomialWeightedQuadraticUnderInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  symbolic : TripleActivityLawReconstructionUnderInputs.Hypotheses p.symbolic (min (ε / 16) (1 / 48))
  optimal : PolynomialWeightedQuadraticUnderInputs.Hypotheses p.optimal ε

theorem article_15_14 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.optimal.channelHeight ∧ (Hypotheses p ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let E := SignedAtomicDistance.distance
          (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1)
            (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L))
        E ≤ (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 3) +
          (N : ℝ) ^ (-4 / 3 + ε) ∧ E ≤ (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨ps, hs⟩ := TripleActivityLawReconstructionUnderInputs.uniform_estimates C ε hε
  obtain ⟨po, hQ, ho⟩ := PolynomialWeightedQuadraticUnderInputs.uniform_weighted c κ hc hBCN C ε hε
  refine ⟨⟨ps, po⟩, hQ, ?_⟩
  intro hgeo
  obtain ⟨NS, _hNS, hs⟩ := hs hgeo.symbolic
  obtain ⟨NO, _hNO, ho⟩ := ho hgeo.optimal 0
  refine ⟨max 10 (max NS NO), by omega, ?_⟩
  intro N hN L hband
  refine ⟨(hs N (by omega) L hband (dyadicBlock N) (subset_refl _)).2, ?_⟩
  have hh := (ho N (by omega) L hband).2
  have hμ : 0 ≤ countMoment (dyadicBlock N) L 1 := by
    rw [← HeterogeneousDirectMaximum.actualMean_eq_countMoment (subset_refl (dyadicBlock N))]
    exact sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  rw [FourthCharlierLawDistance.distance_eq_sequence _ _ _ hμ]
  simpa only [PolynomialWeightedQuadraticUnderInputs.weightedError, pow_zero, one_mul,
    ActualQuadraticSubpowerMoments.original, ActualQuadraticSubpowerMoments.quadratic] using hh

end PaperP1.OptimalTripleReconstructionUnderInputs
