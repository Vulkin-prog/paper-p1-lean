module

public import PaperP1.Probability.MeasureFiniteLaw
public import PaperP1.Probability.AdmissibleIndices
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Data.Fintype.Pi

/-!
# Centered Bernoulli expansion on an arbitrary probability space

Article Proposition 4.1 is a finite-indicator identity, even when the original
sample space is infinite. We push the actual measure to its finite Boolean
observation space, use the checked finite-law expansion, and identify every
coefficient with its Bochner expectation. The resulting singleton masses are
proved to be those of the original count pushforward.

The finite carrier can be the paper's admissible index set `𝓘_N`. No assumption
about independence, equal marginals, regularity or an approximation error is used.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MeasureTheory
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω ι τ : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

/-- Simultaneous observation of all indicators on the finite carrier. -/
def indicatorObservation (J : ι → Ω → Bool) : Ω → (ι → Bool) := fun ω x => J x ω

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_indicatorObservation (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    Measurable (indicatorObservation J) :=
  Measurable.of_eval hJ

def indicatorObservationProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) : FiniteProbability (ι → Bool) :=
  finiteObservationProbability μ (indicatorObservation J) (measurable_indicatorObservation J hJ)

/-- The actual Bochner marginal of an indicator. -/
def measureMarginal (μ : Measure Ω) (J : ι → Ω → Bool) (x : ι) : ℝ :=
  ∫ ω, indicatorValue (J x ω) ∂μ

/-- The actual Bochner centered moment. -/
def measureCenteredMoment (μ : Measure Ω) (J : ι → Ω → Bool) (p : ι → ℝ)
    (I : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ I, (indicatorValue (J x ω) - p x) ∂μ

/-- Finite signed representation of the actual count pushforward. -/
def observedCountLaw (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) : SignedLaw ℝ :=
  countLaw G (indicatorObservationProbability μ J hJ).weight (fun x σ => σ x)

/-- The paper's admissible index set: retain every positive exact marginal. -/
def admissibleIndexSet (G : Finset ι) (μ : Measure Ω) (J : ι → Ω → Bool) : Finset ι :=
  G.filter fun x => 0 < measureMarginal μ J x

omit [Fintype ι] [DecidableEq ι] in
theorem finiteMeasure_countLaw_coeff [Fintype τ] [MeasurableSpace τ]
    [MeasurableSingletonClass τ] (ν : Measure τ) [IsProbabilityMeasure ν]
    (G : Finset ι) (J : ι → τ → Bool) (k : ℕ) :
    (countLaw G (finiteProbabilityOfMeasure ν).weight J).coeff k =
      ν.real {σ | indicatorCount G J σ = k} := by
  classical
  rw [countLaw_coeff]
  change (∑ σ, if indicatorCount G J σ = k then ν.real {σ} else 0) = _
  rw [← Finset.sum_filter, sum_measureReal_singleton]
  congr 1
  ext σ
  simp

/-- The signed-law coefficient is the probability of the original count event. -/
theorem observedCountLaw_coeff (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (k : ℕ) :
    (observedCountLaw G μ J hJ).coeff k = μ.real {ω | indicatorCount G J ω = k} := by
  unfold observedCountLaw indicatorObservationProbability finiteObservationProbability
  rw [finiteMeasure_countLaw_coeff]
  have hset : MeasurableSet {σ : ι → Bool | indicatorCount G (fun x σ => σ x) σ = k} :=
    (MeasurableSet.singleton k).preimage (measurable_of_countable _)
  rw [map_measureReal_apply (measurable_indicatorObservation J hJ) hset]
  rfl

omit [DecidableEq ι] in
theorem measurable_indicatorCount (G : Finset ι) (J : ι → Ω → Bool)
    (hJ : ∀ x, Measurable (J x)) : Measurable (indicatorCount G J) := by
  exact (measurable_of_countable (fun σ : ι → Bool => indicatorCount G (fun x σ => σ x) σ)).comp
    (measurable_indicatorObservation J hJ)

/-- An explicit connection to the ordinary measure-theoretic law of the count. -/
theorem observedCountLaw_coeff_eq_pushforward (G : Finset ι) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (k : ℕ) :
    (observedCountLaw G μ J hJ).coeff k = (μ.map (indicatorCount G J)).real {k} := by
  rw [observedCountLaw_coeff,
    map_measureReal_apply (measurable_indicatorCount G J hJ) (MeasurableSet.singleton k)]
  rfl

theorem observedCountLaw_isProbability (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    IsProbability (observedCountLaw G μ J hJ) :=
  countLaw_isProbability G (indicatorObservationProbability μ J hJ) (fun x σ => σ x)

/-- The finite representation realizes the full original count law as a measure. -/
theorem observedCountLaw_realizes (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    lawMeasure (observedCountLaw G μ J hJ) (observedCountLaw_isProbability G μ J hJ).1 =
      μ.map (indicatorCount G J) := by
  apply Measure.ext_of_singleton
  intro k
  rw [lawMeasure_singleton, observedCountLaw_coeff_eq_pushforward]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem observationMarginal_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (x : ι) :
    exactMarginal (indicatorObservationProbability μ J hJ) (fun i σ => σ i) x =
      measureMarginal μ J x := by
  exact finiteObservation_expectation μ (indicatorObservation J)
    (measurable_indicatorObservation J hJ) (fun σ => indicatorValue (σ x))

theorem admissibleIndexSet_eq_positiveMarginalSet (G : Finset ι) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    admissibleIndexSet G μ J =
      positiveMarginalSet G (indicatorObservationProbability μ J hJ) (fun x σ => σ x) := by
  classical
  simp only [admissibleIndexSet, positiveMarginalSet, observationMarginal_eq]

theorem observedCountLaw_restrict_admissible (G : Finset ι) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    observedCountLaw G μ J hJ = observedCountLaw (admissibleIndexSet G μ J) μ J hJ := by
  unfold observedCountLaw
  rw [admissibleIndexSet_eq_positiveMarginalSet G μ J hJ]
  exact countLaw_restrict_positiveMarginals G (indicatorObservationProbability μ J hJ)
    (fun x σ => σ x)

theorem observationCenteredMoment_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (p : ι → ℝ) (I : Finset ι) :
    centeredMoment (indicatorObservationProbability μ J hJ).weight
      (fun x σ => indicatorValue (σ x)) p I = measureCenteredMoment μ J p I := by
  exact finiteObservation_expectation μ (indicatorObservation J)
    (measurable_indicatorObservation J hJ) (fun σ => ∏ x ∈ I, (indicatorValue (σ x) - p x))

/-- The centered law identity with actual Bochner marginal and centered coefficients. -/
theorem centered_measure_expansion (G : Finset ι) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    observedCountLaw G μ J hJ = ∑ I ∈ G.powerset,
      scalar (measureCenteredMoment μ J (measureMarginal μ J) I) *
        forwardDifference ^ I.card * ∏ x ∈ G \ I, bernoulli (measureMarginal μ J x) := by
  unfold observedCountLaw
  rw [centered_countLaw_expansion G _ _ (measureMarginal μ J)]
  apply Finset.sum_congr rfl
  intro I _
  rw [observationCenteredMoment_eq]

omit [Fintype ι] [DecidableEq ι] in
theorem measureCenteredMoment_empty (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (p : ι → ℝ) : measureCenteredMoment μ J p ∅ = 1 := by
  simp [measureCenteredMoment]

theorem measureCenteredMoment_singleton_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (x : ι) :
    measureCenteredMoment μ J (measureMarginal μ J) {x} = 0 := by
  rw [← observationCenteredMoment_eq μ J hJ]
  have hp : measureMarginal μ J =
      exactMarginal (indicatorObservationProbability μ J hJ) (fun i σ => σ i) := by
    funext i
    exact (observationMarginal_eq μ J hJ i).symm
  rw [hp]
  exact centeredMoment_singleton_eq_zero (indicatorObservationProbability μ J hJ).weight
    (fun i σ => indicatorValue (σ i)) x (indicatorObservationProbability μ J hJ).total_weight

theorem measureMarginal_reference_isProbability (G : Finset ι) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    IsProbability (∏ x ∈ G, bernoulli (measureMarginal μ J x)) := by
  simpa only [observationMarginal_eq] using exactMarginal_reference_isProbability G
    (indicatorObservationProbability μ J hJ) (fun i σ => σ i)

/-- Article Proposition 4.1, with the original measure-theoretic law identified.

The finite carrier represents the paper's admissible start index set. The
conclusions are the complete convolution identity, the unit empty coefficient,
the vanishing singleton coefficients and probability status of all deterministic
complementary Bernoulli products. `observedCountLaw_realizes` identifies its left
side with the actual law `μ.map (indicatorCount G J)`; `measureCenteredMoment`
and `measureMarginal` are Bochner expectations, rather than supplied coefficients.
-/
theorem centered_bernoulli_expansion (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    (observedCountLaw G μ J hJ = ∑ I ∈ (admissibleIndexSet G μ J).powerset,
      scalar (measureCenteredMoment μ J (measureMarginal μ J) I) *
        forwardDifference ^ I.card *
          ∏ x ∈ admissibleIndexSet G μ J \ I, bernoulli (measureMarginal μ J x)) ∧
    measureCenteredMoment μ J (measureMarginal μ J) ∅ = 1 ∧
    (∀ x, measureCenteredMoment μ J (measureMarginal μ J) {x} = 0) ∧
    (∀ I : Finset ι, IsProbability
      (∏ x ∈ admissibleIndexSet G μ J \ I, bernoulli (measureMarginal μ J x))) := by
  refine ⟨?_, measureCenteredMoment_empty μ J _, measureCenteredMoment_singleton_eq_zero μ J hJ,
    fun I => measureMarginal_reference_isProbability (admissibleIndexSet G μ J \ I) μ J hJ⟩
  rw [observedCountLaw_restrict_admissible G μ J hJ]
  exact centered_measure_expansion (admissibleIndexSet G μ J) μ J hJ

end PaperP1.Probability
