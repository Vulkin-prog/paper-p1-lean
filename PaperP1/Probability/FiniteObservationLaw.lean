module

public import PaperP1.Probability.PushforwardMass
public import PaperP1.Probability.FiniteCoupling
public import PaperP1.Probability.FiniteLawEmbedding

/-! # Actual probability laws of arbitrary finite natural observations

The law, ordinary total variation, coupling and every Bochner expectation
are identified with their original finite probability sums.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteObservationLaw

open MeasureTheory Finset PaperP1.Algebra PaperP1.Probability

variable {Ω : Type*} [Fintype Ω]

theorem weight_hasSum (P : FiniteProbability Ω) : HasSum P.weight 1 := by
  have h := hasSum_fintype P.weight
  rwa [P.total_weight] at h

def law (P : FiniteProbability Ω) (Z : Ω → ℕ) : ProbabilityMeasure ℕ :=
  PushforwardMass.law Z P.weight P.weight_nonneg (weight_hasSum P)

theorem realMass_eq (P : FiniteProbability Ω) (Z : Ω → ℕ) (k : ℕ) :
    AtomicProbability.realMass (law P Z) k = finiteExpectation P.weight (fun ω ↦ if Z ω = k then 1 else 0) := by
  classical
  rw [law, PushforwardMass.realMass_law]
  change (∑' ω : ({ω | Z ω = k} : Set Ω), P.weight ω.val) = _
  rw [tsum_subtype ({ω | Z ω = k} : Set Ω) P.weight]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, tsum_fintype, finiteExpectation, mul_ite, mul_one, mul_zero]

theorem coefficient_eq (P : FiniteProbability Ω) (Z : Ω → ℕ) (k : ℕ) :
    (observationLaw P Z).coeff k = finiteExpectation P.weight (fun ω ↦ if Z ω = k then 1 else 0) := by
  classical
  simp [observationLaw, AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, finiteExpectation]

theorem realMass_eq_coeff (P : FiniteProbability Ω) (Z : Ω → ℕ) (k : ℕ) :
    AtomicProbability.realMass (law P Z) k = (observationLaw P Z).coeff k := by
  rw [realMass_eq, coefficient_eq]

theorem totalVariation_eq (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    AtomicProbability.totalVariation (law P Z) (law P W) = lawTotalVariation (observationLaw P Z) (observationLaw P W) := by
  change (∑' k : ℕ, |AtomicProbability.realMass (law P Z) k - AtomicProbability.realMass (law P W) k|) / 2 = _
  unfold lawTotalVariation
  rw [FiniteLawEmbedding.l1Norm_eq_tsum]
  simp only [realMass_eq_coeff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]

theorem coupling (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    AtomicProbability.totalVariation (law P Z) (law P W) ≤ disagreementProbability P Z W := by
  rw [totalVariation_eq]
  exact lawTotalVariation_coupling P Z W

theorem integrable (P : FiniteProbability Ω) (Z : Ω → ℕ) (f : ℕ → ℝ) :
    Integrable f (law P Z : Measure ℕ) := by
  rw [AtomicTests.integrable_iff_summable]
  unfold law
  simp only [PushforwardMass.realMass_law]
  exact PushforwardMass.summable_test_map Z P.weight (fun k ↦ |f k|) (hasSum_fintype _).summable

theorem integral_eq (P : FiniteProbability Ω) (Z : Ω → ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂(law P Z : Measure ℕ)) = finiteExpectation P.weight (fun ω ↦ f (Z ω)) := by
  rw [← AtomicTests.expectation_eq_integral _ _ (integrable P Z f)]
  simpa only [law, tsum_fintype, finiteExpectation] using
    PushforwardMass.expectation_law Z P.weight P.weight_nonneg (weight_hasSum P) f (hasSum_fintype _).summable

end PaperP1.FiniteObservationLaw
