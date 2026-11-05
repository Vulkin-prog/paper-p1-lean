module

public import PaperP1.Asymptotics.FourThirdsQuadraticUpper

/-! # Both complete clauses of main Theorem 15.14

The exact symbolic third-activity estimate and optimal numerical upper
bound hold for the same original law, parameters and threshold.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalTripleReconstruction

open Finset MeasureTheory Model CountObservables

theorem article_15_14 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let E := SignedAtomicDistance.distance
        (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1)
          (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L))
      E ≤ (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 3) +
        (N : ℝ) ^ (-4 / 3 + ε) ∧ E ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨NS, _hNS, hs⟩ := TripleActivityLawReconstruction.uniform_bound C ε hε
  obtain ⟨NO, _hNO, ho⟩ := FourThirdsQuadraticUpper.uniform_exact C ε hε
  refine ⟨10 + NS + NO, by omega, ?_⟩
  intro N hN L hband
  exact ⟨hs N (by omega) L hband (dyadicBlock N) Subset.rfl,
    ho N (by omega) L hband (dyadicBlock N) Subset.rfl⟩

end PaperP1.OptimalTripleReconstruction
