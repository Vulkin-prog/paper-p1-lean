module

public import PaperP1.Probability.PositionalCountProbability
public import PaperP1.Model.PositionalDeletedSupport
public import PaperP1.Model.PositionalObservationLaw
public import PaperP1.Model.PositionalCountMoments
public import PaperP1.Probability.WeightedPoissonNorm

/-! # The actual once-erased count and its deterministic original observation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OnceErasedCount

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw PaperP1.PositionalDeletedFields
  PaperP1.PositionalCountProjection

def law (H : ℝ) (N L : ℕ) : ProbabilityMeasure ℕ :=
  PositionalCountProbability.law (onceLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L)
    (onceLaw_isProbability _ _ _)

def countMean (H : ℝ) (N L : ℕ) : ℝ := ∫ k, (k : ℝ) ∂(law H N L : Measure ℕ)

def poissonDistance (N L : ℕ) : ℝ := AtomicProbability.totalVariation (law (8 * (L + 1) : ℕ) N L)
  (WeightedPoissonNorm.poisson (countMean (8 * (L + 1) : ℕ) N L)
    (integral_nonneg (fun _ ↦ Nat.cast_nonneg _)))

theorem countMean_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ countMean H N L :=
  integral_nonneg (fun _ ↦ Nat.cast_nonneg _)

theorem poissonDistance_nonneg (N L : ℕ) : 0 ≤ poissonDistance N L :=
  AtomicProbability.totalVariation_nonneg _ _

theorem realMass_law (H : ℝ) (N L k : ℕ) : AtomicProbability.realMass (law H N L) k =
    CompletedLaw.coeff k (projection (onceLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L)) :=
  PositionalCountProbability.realMass_law _ _ _

theorem law_eq_observation (H : ℝ) (N L : ℕ) :
    law H N L = PositionalObservationLaw.law (dyadicBlock N) L
      (PositionalPairDeletion.oneCount (GoodEdgeCompression.goodEdges H N L)) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_measureReal_singleton
  intro k
  change AtomicProbability.realMass (law H N L) k = AtomicProbability.realMass
    (PositionalObservationLaw.law (dyadicBlock N) L
      (PositionalPairDeletion.oneCount (GoodEdgeCompression.goodEdges H N L))) k
  rw [realMass_law, onceLaw_finite_mixture, map_sum, map_sum]
  have hc (v : Configuration ℕ) := PositionalCountProbability.onceKernel_coeff
    (GoodEdgeCompression.goodEdges H N L) v (fun e he ↦ RetainedGoodEdges.good_pair_card H N L e he) k
  simp only [map_smul, hc, smul_eq_mul]
  rw [PositionalObservationLaw.law, FiniteObservationLaw.realMass_eq]
  rfl

theorem integral_law (H : ℝ) (N L : ℕ) (g : ℕ → ℝ) :
    (∫ k, g k ∂(law H N L : Measure ℕ)) = ∫ ω,
      g (PositionalPairDeletion.oneCount (GoodEdgeCompression.goodEdges H N L)
        (configuration (dyadicBlock N) (fun x ↦ infiniteStartIndicator x L) ω)) ∂infiniteRademacherMeasure := by
  rw [law_eq_observation, PositionalObservationLaw.integral_law]

theorem countMean_eq_sum (H : ℝ) (N L : ℕ) :
    countMean H N L = ∑ x ∈ dyadicBlock N, PositionalFactorialCovariance.mean
      (onceLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L) x := by
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges H N L
  have hs0 := (PositionalCountMoments.weighted_moment_bound G L 2).1
  have hs := PositionalDeletionKernels.once_polynomial_moment_bound E (original G L)
    (original_isProbability G L).1 2 (by
      simpa only [original, CompletedPositionalLaw.coeff_ofFinite] using hs0)
  exact PositionalCountProbability.mean_eq_sum G (onceLaw E G L) (onceLaw_isProbability E G L)
    (PositionalDeletedSupport.once_supported E G L) hs.1

end PaperP1.OnceErasedCount
