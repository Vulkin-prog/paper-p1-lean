module

public import PaperP1.Probability.PalmPolynomial
public import PaperP1.Probability.CenteredMeasureExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Signed Palm laws on an arbitrary probability space

The finite observation is the entire indicator vector. Its exact weights,
joint moments and conditional probabilities are identified with the original
measure; no finite original sample space is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MeasureSignedPalm

open MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.IndicatorDeletion
  PaperP1.FiniteSignedPalm PaperP1.ConditionalPalm PaperP1.FactorialGeneratingPolynomial
  PaperP1.PalmPolynomial PaperP1.FiniteLawShift Polynomial Finset

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

def observedMean (G : Finset ι) (μ : Measure Ω) (J : ι → Ω → Bool) : ℝ :=
  ∫ ω, (indicatorCount G J ω : ℝ) ∂μ

def observedJointMoment (μ : Measure Ω) (J : ι → Ω → Bool) (A : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicatorValue (J x ω) : ℝ) ∂μ

def observedBinomialMoment (G : Finset ι) (μ : Measure Ω) (J : ι → Ω → Bool) (j : ℕ) : ℝ :=
  ∫ ω, ((indicatorCount G J ω).choose j : ℝ) ∂μ

def observedPalm (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) : SignedLaw ℝ :=
  conditionalPalm G (indicatorObservationProbability μ J hJ) (fun x σ ↦ σ x)

def observedRecurrenceNorm (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (θ : ℝ) : ℝ :=
  recurrenceNorm G (indicatorObservationProbability μ J hJ) (fun x σ ↦ σ x) θ

omit [Fintype ι] [DecidableEq ι] in
theorem measureMarginal_eq_event (μ : Measure Ω) (J : ι → Ω → Bool)
    (x : ι) (hJx : Measurable (J x)) :
    measureMarginal μ J x = μ.real {ω | J x ω = true} := by
  have hset : MeasurableSet {ω | J x ω = true} :=
    (measurableSet_singleton true).preimage hJx
  simpa only [measureMarginal, indicatorValue, Set.indicator_apply, Pi.one_apply,
    Set.mem_ofPred_eq] using integral_indicator_one (μ := μ) hset

theorem observation_mean_eq (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    mean G (indicatorObservationProbability μ J hJ) (fun x σ ↦ σ x) = observedMean G μ J := by
  unfold mean observedMean indicatorObservationProbability
  have h := finiteObservation_expectation μ (indicatorObservation J) (measurable_indicatorObservation J hJ)
    (fun σ ↦ (indicatorCount G (fun x τ ↦ τ x) σ : ℝ))
  have hcount (ω : Ω) : indicatorCount G (fun x σ ↦ σ x) (indicatorObservation J ω) =
      indicatorCount G J ω := rfl
  simpa only [hcount] using h

theorem observedRecurrenceNorm_eq_tsum (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (θ : ℝ) :
    observedRecurrenceNorm G μ J hJ θ =
      ∑' k : ℕ, |(k : ℝ) * (observedCountLaw G μ J hJ).coeff k -
        (observedMean G μ J - θ) * extendedCoefficient (observedCountLaw G μ J hJ) ((k : ℤ) - 1) -
          θ * extendedCoefficient (observedCountLaw G μ J hJ) ((k : ℤ) - 2)| := by
  unfold observedRecurrenceNorm
  rw [recurrenceNorm_eq_tsum, observation_mean_eq]
  rfl

theorem observation_jointMoment_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (A : Finset ι) :
    jointMoment (indicatorObservationProbability μ J hJ).weight (fun x σ ↦ σ x) A =
      observedJointMoment μ J A :=
  finiteObservation_expectation μ (indicatorObservation J) (measurable_indicatorObservation J hJ)
    (fun σ ↦ ∏ x ∈ A, (indicatorValue (σ x) : ℝ))

theorem observation_binomialMoment_eq (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (j : ℕ) :
    finiteExpectation (indicatorObservationProbability μ J hJ).weight
        (fun σ ↦ ((indicatorCount G (fun x τ ↦ τ x) σ).choose j : ℝ)) =
      observedBinomialMoment G μ J j := by
  unfold observedBinomialMoment indicatorObservationProbability
  have h := finiteObservation_expectation μ (indicatorObservation J) (measurable_indicatorObservation J hJ)
    (fun σ ↦ ((indicatorCount G (fun x τ ↦ τ x) σ).choose j : ℝ))
  have hcount (ω : Ω) : indicatorCount G (fun x σ ↦ σ x) (indicatorObservation J ω) =
      indicatorCount G J ω := rfl
  simpa only [hcount] using h

def observedConditionalLaw (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (x : ι)
    (hp : 0 < measureMarginal μ J x) : SignedLaw ℝ :=
  countLaw (G.erase x)
    (conditionalProbability (indicatorObservationProbability μ J hJ) (fun y σ ↦ σ y) x
      (by simpa only [observationMarginal_eq] using hp)).weight (fun y σ ↦ σ y)

theorem observedConditionalLaw_isProbability (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (x : ι)
    (hp : 0 < measureMarginal μ J x) :
    Probability.IsProbability (observedConditionalLaw G μ J hJ x hp) := by
  unfold observedConditionalLaw
  exact countLaw_isProbability _ _ _

theorem observedConditionalLaw_coeff (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (x : ι)
    (hp : 0 < measureMarginal μ J x) (k : ℕ) :
    (observedConditionalLaw G μ J hJ x hp).coeff k =
      μ.real {ω | J x ω = true ∧ indicatorCount (G.erase x) J ω = k} / measureMarginal μ J x := by
  classical
  unfold observedConditionalLaw
  rw [conditional_countLaw_coeff, observationMarginal_eq]
  unfold indicatorObservationProbability
  rw [finiteObservation_expectation μ (indicatorObservation J)
    (measurable_indicatorObservation J hJ)]
  have hset : MeasurableSet {ω | J x ω = true ∧ indicatorCount (G.erase x) J ω = k} :=
    ((measurableSet_singleton true).preimage (hJ x)).inter
      ((measurableSet_singleton k).preimage (measurable_indicatorCount (G.erase x) J hJ))
  have hind : (∫ ω, (if J x ω = true ∧ indicatorCount (G.erase x) J ω = k then 1 else 0 : ℝ) ∂μ) =
      μ.real {ω | J x ω = true ∧ indicatorCount (G.erase x) J ω = k} := by
    simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
      integral_indicator_one (μ := μ) hset
  change (∫ ω, (if J x ω = true ∧ indicatorCount (G.erase x) J ω = k then 1 else 0 : ℝ) ∂μ) /
    measureMarginal μ J x = _
  rw [hind]

theorem observedPalm_eq_conditional_sum (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    observedPalm G μ J hJ = ∑ x ∈ G, if hp : 0 < measureMarginal μ J x then
      scalar (measureMarginal μ J x) *
        (observedConditionalLaw G μ J hJ x hp - observedCountLaw (G.erase x) μ J hJ) else 0 := by
  unfold observedPalm conditionalPalm
  apply sum_congr rfl
  intro x _
  simp only [observationMarginal_eq, observedConditionalLaw, observedCountLaw]

theorem observed_signed_palm_bound (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (θ : ℝ) :
    |observedRecurrenceNorm G μ J hJ θ - l1Norm (observedPalm G μ J hJ -
      scalar θ * forwardDifference * observedCountLaw G μ J hJ)| ≤
        2 * ∑ x ∈ G, (measureMarginal μ J x) ^ 2 := by
  simpa only [observedRecurrenceNorm, observedPalm, observedCountLaw, observationMarginal_eq] using
    conditionalPalm_residual_bound G (indicatorObservationProbability μ J hJ) (fun x σ ↦ σ x) θ

theorem observed_palm_coefficient (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (j : ℕ) :
    (transform (observedPalm G μ J hJ)).coeff j =
      ∑ A ∈ G.powersetCard j, ∑ x ∈ G \ A,
        (observedJointMoment μ J (insert x A) - measureMarginal μ J x * observedJointMoment μ J A) := by
  unfold observedPalm
  rw [conditionalPalm_eq_palmDifference, palm_coefficient]
  simp only [observationMarginal_eq, observation_jointMoment_eq]

theorem observed_uniform_palm_coefficient (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (p : ℝ)
    (hp : ∀ x ∈ G, measureMarginal μ J x = p) (j : ℕ) :
    (transform (observedPalm G μ J hJ)).coeff j =
      (j + 1 : ℝ) * observedBinomialMoment G μ J (j + 1) -
        p * ((G.card : ℝ) - j) * observedBinomialMoment G μ J j := by
  unfold observedPalm
  rw [conditionalPalm_eq_palmDifference]
  have hp' : ∀ x ∈ G, exactMarginal (indicatorObservationProbability μ J hJ) (fun y σ ↦ σ y) x = p := by
    simpa only [observationMarginal_eq] using hp
  rw [uniform_palm_coefficient G _ _ p hp', observation_binomialMoment_eq,
    observation_binomialMoment_eq]

/-- Every assertion of the signed Palm proposition, on the original
probability space with its exact (possibly zero) individual marginals. -/
theorem companion_T19_12 (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) (θ : ℝ) :
    |observedRecurrenceNorm G μ J hJ θ - l1Norm (observedPalm G μ J hJ -
      scalar θ * forwardDifference * observedCountLaw G μ J hJ)| ≤
        2 * ∑ x ∈ G, (measureMarginal μ J x) ^ 2 ∧
      (∀ j : ℕ, (transform (observedPalm G μ J hJ)).coeff j =
        ∑ A ∈ G.powersetCard j, ∑ x ∈ G \ A,
          (observedJointMoment μ J (insert x A) - measureMarginal μ J x * observedJointMoment μ J A)) ∧
      (∀ p : ℝ, (∀ x ∈ G, measureMarginal μ J x = p) → ∀ j : ℕ,
        (transform (observedPalm G μ J hJ)).coeff j =
          (j + 1 : ℝ) * observedBinomialMoment G μ J (j + 1) -
            p * ((G.card : ℝ) - j) * observedBinomialMoment G μ J j) :=
  ⟨observed_signed_palm_bound G μ J hJ θ, observed_palm_coefficient G μ J hJ,
    fun p hp ↦ observed_uniform_palm_coefficient G μ J hJ p hp⟩

end PaperP1.MeasureSignedPalm
