module

public import PaperP1.Probability.PositionalCountCumulant
public import PaperP1.Probability.PositionalDeletionKernels

/-! # The genuine total-count probability law of a positive completed field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCountProbability

open Finset MeasureTheory PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositivePositionalConvolution PaperP1.PositionalCountProjection
  PaperP1.PositionalFactorialCovariance PaperP1.PositionalGroundSupport PaperP1.PositionalTotalMass

variable {ι : Type*}

def law (ν : Space ι) (hν : IsProbability ν) : ProbabilityMeasure ℕ :=
  PushforwardMass.law totalCount (fun v ↦ coeff v ν) hν.1
    (hasSum_coeff_of_totalMass_eq_one ν hν.2)

theorem realMass_law (ν : Space ι) (hν : IsProbability ν) (k : ℕ) :
    AtomicProbability.realMass (law ν hν) k = CompletedLaw.coeff k (projection ν) := by
  rw [law, PushforwardMass.realMass_law, projection_coeff]

theorem mean_eq (ν : Space ι) (hν : IsProbability ν)
    (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    (∫ k, (k : ℝ) ∂(law ν hν : Measure ℕ)) = ∑' v, coeff v ν * (totalCount v : ℝ) := by
  have hfirst : Summable (fun v ↦ coeff v ν * (totalCount v : ℝ)) :=
    FiniteMomentComparison.summable_test _ _ _ hν.1 (fun _ ↦ by positivity) (fun v ↦ by
      dsimp only [weight]
      have ht : (0 : ℝ) ≤ totalCount v := by positivity
      nlinarith) hs
  have hscalar := PushforwardMass.summable_test_map totalCount (fun v ↦ coeff v ν)
    (fun k ↦ (k : ℝ)) hfirst
  have hint : Integrable (fun k : ℕ ↦ (k : ℝ)) (law ν hν : Measure ℕ) := by
    rw [AtomicTests.integrable_iff_summable]
    have he (k : ℕ) : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    simpa only [law, PushforwardMass.realMass_law, he] using hscalar
  rw [← AtomicTests.expectation_eq_integral _ _ hint]
  exact PushforwardMass.expectation_law _ _ _ _ _ hfirst

theorem mean_eq_sum (G : Finset ι) (ν : Space ι) (hν : IsProbability ν)
    (hground : Supported G ν) (hs : Summable (fun v ↦ coeff v ν * weight v)) :
    (∫ k, (k : ℝ) ∂(law ν hν : Measure ℕ)) = ∑ x ∈ G, mean ν x := by
  rw [mean_eq ν hν hs]
  exact (PositionalCountCumulant.sum_mean G ν hν.1 hground hs).symm

theorem onceKernel_coeff (E : Finset (Finset ι)) (v : Configuration ι)
    (hE : ∀ e ∈ E, e.card = 2) (k : ℕ) :
    CompletedLaw.coeff k (projection (PositionalDeletionKernels.onceKernel E v)) =
      if PositionalPairDeletion.oneCount E v = k then 1 else 0 := by
  classical
  rw [← (hasSum_projection_coeff (PositionalDeletionKernels.onceKernel E v) k).tsum_eq]
  have hh := (PositionalDeletionKernels.onceKernel_count_test E v hE
    (fun n ↦ if n = k then (1 : ℝ) else 0)).tsum_eq
  convert hh using 1
  apply tsum_congr
  intro w
  by_cases hw : totalCount w = k <;> simp [hw]

end PaperP1.PositionalCountProbability
