module

public import PaperP1.Probability.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# From arbitrary probability spaces to finite laws

Every finite-valued measurable observation of an arbitrary probability space
has an actual finite probability distribution. This module connects the real
singleton weights to measures and Bochner expectations. Measurability remains
explicit, so the totalized behavior of `Measure.map` on nonmeasurable functions
cannot silently supply a probability-law interpretation.
-/

@[expose] public noncomputable section

open scoped BigOperators
open MeasureTheory
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω τ : Type*} [MeasurableSpace Ω] [Fintype τ]
  [MeasurableSpace τ] [MeasurableSingletonClass τ]

/-- Atomic measure associated with a coefficientwise nonnegative finite law.

The proof argument prevents using this construction to identify a signed
expansion term with a positive measure. The measure is characterized by the
singleton identity below.
-/
def lawMeasure (ν : SignedLaw ℝ) (_hν : ∀ k, 0 ≤ ν.coeff k) : Measure ℕ :=
  Measure.sum fun k => ENNReal.ofReal (ν.coeff k) • Measure.dirac k

theorem lawMeasure_singleton (ν : SignedLaw ℝ) (hν : ∀ k, 0 ≤ ν.coeff k) (k : ℕ) :
    lawMeasure ν hν {k} = ENNReal.ofReal (ν.coeff k) := by
  rw [lawMeasure, Measure.sum_apply _ (MeasurableSet.singleton k)]
  simp [Measure.smul_apply, Set.indicator_apply, eq_comm]

/-- The actual singleton masses of a probability measure on a finite space. -/
def finiteProbabilityOfMeasure (ν : Measure τ) [IsProbabilityMeasure ν] : FiniteProbability τ where
  weight := fun x => ν.real {x}
  weight_nonneg := fun _ => measureReal_nonneg
  total_weight := by
    rw [sum_measureReal_singleton]
    simp

/-- Every real-valued function on a finite space is integrable for a finite measure. -/
theorem integrable_finite_function (ν : Measure τ) [IsFiniteMeasure ν] (f : τ → ℝ) :
    Integrable f ν := by
  rw [← integrableOn_univ]
  exact IntegrableOn.of_finite Set.finite_univ

/-- Finite weighted expectation is exactly the Bochner expectation. -/
theorem finiteExpectation_of_measure (ν : Measure τ) [IsProbabilityMeasure ν] (f : τ → ℝ) :
    finiteExpectation (finiteProbabilityOfMeasure ν).weight f = ∫ x, f x ∂ν := by
  rw [integral_fintype (integrable_finite_function ν f)]
  rfl

/-- Pushforward weights constructed from a measurable finite-valued observation. -/
def finiteObservationProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → τ) (_hF : Measurable F) : FiniteProbability τ :=
  finiteProbabilityOfMeasure (μ.map F)

theorem finiteObservationProbability_weight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → τ) (hF : Measurable F) (x : τ) :
    (finiteObservationProbability μ F hF).weight x = μ.real (F ⁻¹' {x}) := by
  exact map_measureReal_apply hF (MeasurableSet.singleton x)

/-- Expectation is preserved by the finite observation, with measurability explicit. -/
theorem finiteObservation_expectation (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → τ) (hF : Measurable F) (f : τ → ℝ) :
    finiteExpectation (finiteObservationProbability μ F hF).weight f =
      ∫ ω, f (F ω) ∂μ := by
  rw [finiteObservationProbability, finiteExpectation_of_measure]
  exact integral_map hF.aemeasurable (integrable_finite_function (μ.map F) f).aestronglyMeasurable

end PaperP1.Probability
