module

public import PaperP1.Probability.StoppedFiniteLaw
public import PaperP1.Probability.CenteredMeasureExpansion

/-!
# Positive stopped remainder on an arbitrary probability space

Article Proposition 5.2: the remainder kernel is constructed from the actual
joint prefix activity and the actual, possibly dependent, suffix count. Its
coefficients are identified with Bochner expectations; its mass and ordinary
ℓ¹ norm are the joint activation probability. The resulting error bound has
no suffix-size factor and no independence hypothesis.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MeasureTheory
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]

def measureJointMoment (μ : Measure Ω) (J : ι → Ω → Bool) (I : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ I, (indicatorValue (J x ω) : ℝ) ∂μ

def measureRetainedReference (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : SignedLaw ℝ :=
  ∑ I ∈ retainedSets G D, scalar (measureJointMoment μ J I) * forwardDifference ^ I.card

def measureBoundaryKernel (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) : SignedLaw ℝ :=
  finiteBoundaryKernel G (indicatorObservationProbability μ J hJ) (fun x σ => σ x) I

theorem observationJointMoment_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) :
    finiteJointMoment (indicatorObservationProbability μ J hJ) (fun x σ => σ x) I =
      measureJointMoment μ J I := by
  exact finiteObservation_expectation μ (indicatorObservation J)
    (measurable_indicatorObservation J hJ) (fun σ => ∏ x ∈ I, (indicatorValue (σ x) : ℝ))

/-- The joint moment is exactly the probability that every prefix indicator is active. -/
theorem measureJointMoment_eq_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) :
    measureJointMoment μ J I = μ.real {ω | ∀ x ∈ I, J x ω = true} := by
  classical
  rw [← observationJointMoment_eq μ J hJ]
  unfold finiteJointMoment indicatorObservationProbability finiteObservationProbability
  simp_rw [indicator_product_eq_indicator (fun x (σ : ι → Bool) => σ x) I]
  have hset : MeasurableSet {σ : ι → Bool | ∀ x ∈ I, σ x = true} :=
    (Set.to_countable _).measurableSet
  calc
    _ = (μ.map (indicatorObservation J)).real {σ : ι → Bool | ∀ x ∈ I, σ x = true} := by
      convert finiteMeasure_indicator_expectation (μ.map (indicatorObservation J))
        (fun σ : ι → Bool => ∀ x ∈ I, σ x = true) using 1
      congr 1
      funext σ
      split_ifs <;> simp_all
    _ = _ := map_measureReal_apply (measurable_indicatorObservation J hJ) hset

theorem measureJointMoment_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) :
    measureJointMoment μ J I ≤ 1 := by
  rw [measureJointMoment_eq_probability μ J hJ]
  exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ

theorem measureRetainedReference_eq (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    measureRetainedReference G D μ J =
      retainedCountReference G D (indicatorObservationProbability μ J hJ) (fun x σ => σ x) := by
  simp only [measureRetainedReference, retainedCountReference, observationJointMoment_eq]

theorem measureRetainedReference_mass (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ι → Ω → Bool)
    (hJ : ∀ x, Measurable (J x)) (h_empty : D ∅) :
    totalMass (measureRetainedReference G D μ J) = 1 := by
  rw [measureRetainedReference_eq G D μ J hJ]
  exact retainedCountReference_mass G D (indicatorObservationProbability μ J hJ) (fun x σ => σ x) h_empty

theorem measureBoundaryKernel_nonneg (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) (k : ℕ) :
    0 ≤ (measureBoundaryKernel G μ J hJ I).coeff k :=
  finiteBoundaryKernel_nonneg G (indicatorObservationProbability μ J hJ) (fun x σ => σ x) I k

/-- Every mass is the expected prefix indicator times the suffix count event. -/
theorem measureBoundaryKernel_coeff (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) (k : ℕ) :
    (measureBoundaryKernel G μ J hJ I).coeff k =
      ∫ ω, (∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) *
        (if indicatorCount (orderedSuffix G I) J ω = k then 1 else 0) ∂μ := by
  classical
  unfold measureBoundaryKernel finiteBoundaryKernel
  rw [countLaw_coeff]
  calc
    _ = finiteExpectation (indicatorObservationProbability μ J hJ).weight
        (fun σ => (∏ x ∈ I, (indicatorValue (σ x) : ℝ)) *
          (if indicatorCount (orderedSuffix G I) (fun x σ => σ x) σ = k then 1 else 0)) := by
      unfold finiteExpectation
      apply Finset.sum_congr rfl
      intro σ _
      dsimp only
      split_ifs <;> simp_all
    _ = _ := finiteObservation_expectation μ (indicatorObservation J)
      (measurable_indicatorObservation J hJ)
      (fun σ => (∏ x ∈ I, (indicatorValue (σ x) : ℝ)) *
        (if indicatorCount (orderedSuffix G I) (fun x σ => σ x) σ = k then 1 else 0))

theorem measureBoundaryKernel_mass (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) :
    totalMass (measureBoundaryKernel G μ J hJ I) = measureJointMoment μ J I := by
  rw [measureBoundaryKernel, finiteBoundaryKernel_mass, observationJointMoment_eq]

theorem measureBoundaryKernel_l1Norm (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (I : Finset ι) :
    l1Norm (measureBoundaryKernel G μ J hJ I) = measureJointMoment μ J I := by
  rw [l1Norm_eq_totalMass_of_nonneg _ (measureBoundaryKernel_nonneg G μ J hJ I),
    measureBoundaryKernel_mass]

theorem stopped_measure_count_difference (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ι → Ω → Bool)
    (hJ : ∀ x, Measurable (J x)) (hD : Hereditary D) (h_empty : D ∅) :
    observedCountLaw G μ J hJ - measureRetainedReference G D μ J =
      ∑ I ∈ boundarySets G D, forwardDifference ^ I.card * measureBoundaryKernel G μ J hJ I := by
  rw [measureRetainedReference_eq G D μ J hJ]
  exact stopped_finite_count_difference G D (indicatorObservationProbability μ J hJ)
    (fun x σ => σ x) hD h_empty

theorem stopped_measure_count_l1_bound (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ι → Ω → Bool)
    (hJ : ∀ x, Measurable (J x)) (hD : Hereditary D) (h_empty : D ∅) :
    l1Norm (observedCountLaw G μ J hJ - measureRetainedReference G D μ J) ≤
      ∑ I ∈ boundarySets G D, (2 : ℝ) ^ I.card * measureJointMoment μ J I := by
  rw [measureRetainedReference_eq G D μ J hJ]
  simpa only [observedCountLaw, observationJointMoment_eq] using stopped_finite_count_l1_bound G D
    (indicatorObservationProbability μ J hJ) (fun x σ => σ x) hD h_empty

/-- Article Proposition 5.2, including the positive kernel's exact mass and norm bound. -/
theorem positive_stopped_remainder (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ι → Ω → Bool)
    (hJ : ∀ x, Measurable (J x)) (hD : Hereditary D) (h_empty : D ∅) :
    (observedCountLaw G μ J hJ - measureRetainedReference G D μ J =
      ∑ I ∈ boundarySets G D, forwardDifference ^ I.card * measureBoundaryKernel G μ J hJ I) ∧
    (∀ I k, 0 ≤ (measureBoundaryKernel G μ J hJ I).coeff k) ∧
    (∀ I, totalMass (measureBoundaryKernel G μ J hJ I) = measureJointMoment μ J I) ∧
    l1Norm (observedCountLaw G μ J hJ - measureRetainedReference G D μ J) ≤
      ∑ I ∈ boundarySets G D, (2 : ℝ) ^ I.card * measureJointMoment μ J I :=
  ⟨stopped_measure_count_difference G D μ J hJ hD h_empty,
    measureBoundaryKernel_nonneg G μ J hJ, measureBoundaryKernel_mass G μ J hJ,
    stopped_measure_count_l1_bound G D μ J hJ hD h_empty⟩

end PaperP1.Probability
