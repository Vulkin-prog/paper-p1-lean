module

public import PaperP1.Asymptotics.FourThirdsQuadraticUpper
public import PaperP1.Asymptotics.ActualHermiteReferenceRate
public import PaperP1.Asymptotics.ActualReferenceProbability
public import PaperP1.Asymptotics.ExplicitHermiteLaw

/-! # Complete main Corollary 19.1 for the actual single/double-jump Hermite laws

Both the exact original parameters and every fixed-height explicit reference
are retained. No matching lower bound is asserted for the exact reference.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalHermite

open Finset MeasureTheory Model CountObservables FiniteChannelHierarchy
  ChannelMassPhaseEquivalent

theorem article_19_1_exact (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let μ := countMoment (dyadicBlock N) L 1
      let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
      ∃ hα : 0 ≤ α, ∃ hαμ : α ≤ μ,
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (CompletedLaw.toSignedMeasure (HermiteReference.reference μ α)) ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
        AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
          (HermiteReference.law μ α hα hαμ) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨NO, _hNO, ho⟩ := FourThirdsQuadraticUpper.uniform_exact C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := ActualHermiteReferenceRate.uniform_comparison C (ε / 2) (by positivity)
  obtain ⟨NH, _hNH, hh⟩ := ActualReferenceProbability.hermite_parameters C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NO + NP + NH + NF, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let μ := countMoment (dyadicBlock N) L 1
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  obtain ⟨hα, hαμ⟩ := hh N (by omega) L hband
  have hμ : 0 ≤ μ := hα.le.trans hαμ.le
  refine ⟨hα.le, hαμ.le, ?_⟩
  have hq := ho N (by omega) L hband (dyadicBlock N) Subset.rfl
  have hr := hp N (by omega) L hband (dyadicBlock N) Subset.rfl μ hμ
  have ht := SignedAtomicDistance.triangle (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
    (QuadraticPoisson.reference μ α) (CompletedLaw.toSignedMeasure (HermiteReference.reference μ α))
  have herror : SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (CompletedLaw.toSignedMeasure (HermiteReference.reference μ α)) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
    have hb : 2 * (N : ℝ) ^ (-4 / 3 + ε / 2) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
      simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)
    linarith only [hq, hr, ht, hb]
  refine ⟨herror, ?_⟩
  have hd := SignedAtomicDistance.probability_eq (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
    (HermiteReference.law μ α hα.le hαμ.le)
  rw [← HermiteReference.actual_signed_reference μ α hα.le hαμ.le] at hd
  have hn := Real.rpow_nonneg (Nat.cast_nonneg N) (-4 / 3 + ε)
  linarith only [hd, herror, hn]

theorem article_19_1 (C ε : ℝ) (hε : 0 < ε) :
    (∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let μ := countMoment (dyadicBlock N) L 1
      let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
      ∃ hα : 0 ≤ α, ∃ hαμ : α ≤ μ,
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (CompletedLaw.toSignedMeasure (HermiteReference.reference μ α)) ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
        AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
          (HermiteReference.law μ α hα hαμ) ≤ (N : ℝ) ^ (-4 / 3 + ε)) ∧
    (∀ h : ℕ, 3 ≤ h → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (CompletedLaw.toSignedMeasure (HermiteReference.reference (nominalMean N L) (coefficient N L h))) ≤
        (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε)) ∧
    (∀ h : ℕ, 3 ≤ h → ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ H : ProbabilityMeasure ℕ,
        (H : Measure ℕ).toSignedMeasure = CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L h)) ∧
        0 < AdjacentReferencePhase.leadingGap N L h ∧
        |AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) H /
          (phaseMass N L (h + 1) * PoissonDifferenceSigned.norm (nominalMean N L) 2 / 4) - 1| ≤ τ) :=
  ⟨article_19_1_exact C ε hε, fun h hh ↦ ExplicitHermiteLaw.uniform_bound h hh C ε hε,
    fun h hh ↦ ExplicitHermiteLaw.uniform_probability_equivalent h hh C⟩

end PaperP1.OptimalHermite
