module

public import PaperP1.Probability.InfiniteCylinderTransfer
public import PaperP1.Probability.MeasureFiniteLaw

/-!
# Exact expectation transport from the infinite prime signs

The finite product measure has exactly the normalized real weights used in
the finite algebra. Consequently every finite-cylinder observable has the
same actual Bochner expectation in the infinite model.
-/

@[expose] public noncomputable section

open MeasureTheory
open PaperP1.Arithmetic PaperP1.Model PaperP1.Algebra
open PaperP1.Model.InfiniteRademacher
open PaperP1.Probability.InfiniteCylinderTransfer

namespace PaperP1.Probability.CylinderExpectations

local instance : MeasurableSpace F₂ := ⊤

theorem measurable_restrictToFinite (M : ℕ) : Measurable (restrictToFinite M) := by
  exact Measurable.of_eval fun p => measurable_pi_apply (finitePrimeCoordinate M p)

theorem finiteCylinder_real_singleton (M : ℕ) (σ : SampleSpace M) :
    (finiteRademacherMeasure M).real {σ} = (cylinderProbability M).weight σ := by
  rw [Measure.real, finiteRademacherMeasure_singleton]
  simp [cylinderProbability, uniformFiniteProbability, SampleSpace,
    ZMod.card, ENNReal.toReal_pow]

theorem finiteCylinder_weights_eq (M : ℕ) :
    (finiteProbabilityOfMeasure (finiteRademacherMeasure M)).weight =
      (cylinderProbability M).weight := by
  funext σ
  exact finiteCylinder_real_singleton M σ

theorem finiteCylinder_integral (M : ℕ) (f : SampleSpace M → ℝ) :
    (∫ σ, f σ ∂finiteRademacherMeasure M) =
      finiteExpectation (cylinderProbability M).weight f := by
  rw [← finiteExpectation_of_measure, finiteCylinder_weights_eq]

theorem infiniteCylinder_integral (M : ℕ) (f : SampleSpace M → ℝ) :
    (∫ ω, f (restrictToFinite M ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability M).weight f := by
  have hmap := integral_map (measurable_restrictToFinite M).aemeasurable
    (integrable_finite_function (infiniteRademacherMeasure.map (restrictToFinite M)) f).aestronglyMeasurable
  rw [map_infiniteRademacherMeasure_restrictToFinite] at hmap
  exact hmap.symm.trans (finiteCylinder_integral M f)

theorem finiteCylinder_event (M : ℕ) (E : SampleSpace M → Prop) [DecidablePred E] :
    (finiteRademacherMeasure M).real {σ | E σ} =
      finiteExpectation (cylinderProbability M).weight (fun σ => if E σ then 1 else 0) := by
  rw [← finiteMeasure_indicator_expectation, finiteCylinder_weights_eq]

end PaperP1.Probability.CylinderExpectations
