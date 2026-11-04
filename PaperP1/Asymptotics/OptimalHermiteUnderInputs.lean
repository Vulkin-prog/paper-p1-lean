module

public import PaperP1.Asymptotics.PolynomialWeightedQuadraticUnderInputs
public import PaperP1.Asymptotics.ActualHermiteReferenceRateUnderInputs
public import PaperP1.Asymptotics.ExplicitHermiteLawUnderInputs

/-! # Optimal-power original-law approximation by the actual single/double-jump Hermite law

Together with ExplicitHermiteLawUnderInputs.uniform_bound and its moving
equivalent, this supplies the exact-parameter clause of article19.1. The law
is the existing actual pushforward of two independent Poisson variables.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalHermiteUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.CountObservables

structure Parameters where
  optimal : PolynomialWeightedQuadraticUnderInputs.Parameters
  pair : FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  optimal : PolynomialWeightedQuadraticUnderInputs.Hypotheses p.optimal (ε / 2)
  pair : FinitePairDeficitInputs.Hypotheses p.pair (GeneralGraphHostCount.sizeCap (1 / 100))

theorem article_19_1_exact (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.optimal.channelHeight ∧ (Hypotheses p ε →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let μ := countMoment (dyadicBlock N) L 1
        let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
        ∃ hα : 0 ≤ α, ∃ hαμ : α ≤ μ,
          SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
            (CompletedLaw.toSignedMeasure (HermiteReference.reference μ α)) ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
          AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
            (HermiteReference.law μ α hα hαμ) ≤ (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨po, hQ, ho⟩ := PolynomialWeightedQuadraticUnderInputs.uniform_weighted c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨pp, hp⟩ := ActualHermiteReferenceRateUnderInputs.uniform_comparison C (ε / 2) (by positivity)
  obtain ⟨NH, _hNH, hh⟩ := PositiveSecondCumulant.uniform_hermite_admissibility c κ hc hBCN C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨po, pp⟩, hQ, ?_⟩
  intro hgeo
  obtain ⟨NO, _hNO, ho⟩ := ho hgeo.optimal 0
  obtain ⟨NP, _hNP, hp⟩ := hp hgeo.pair
  refine ⟨max 10 (max NO (max NP (max NH NF))), by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let μ := countMoment (dyadicBlock N) L 1
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  obtain ⟨hα, hαμ⟩ := hh N (by omega) L hband
  have hμ : 0 ≤ μ := hα.le.trans hαμ.le
  refine ⟨hα.le, hαμ.le, ?_⟩
  have hq : SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (QuadraticPoisson.reference μ α) ≤ (N : ℝ) ^ (-4 / 3 + ε / 2) := by
    rw [FourthCharlierLawDistance.distance_eq_sequence _ _ _ hμ]
    simpa only [PolynomialWeightedQuadraticUnderInputs.weightedError, pow_zero, one_mul,
      ActualQuadraticSubpowerMoments.original, ActualQuadraticSubpowerMoments.quadratic] using (ho N (by omega) L hband).2
  have hr := hp N (by omega) L hband (dyadicBlock N) (subset_refl _) μ hμ
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

end PaperP1.OptimalHermiteUnderInputs
