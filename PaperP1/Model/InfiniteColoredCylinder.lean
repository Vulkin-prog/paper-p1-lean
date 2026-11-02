module

public import PaperP1.Model.InfiniteColoredSamples
public import PaperP1.Probability.UniformFubini

/-! # Exact uniform finite-event probabilities in the actual infinite colored replica space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteColoredCylinder

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Probability
  PaperP1.Model.InfiniteRademacher PaperP1.InfiniteColoredSamples PaperP1.UniformFubini
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance infiniteColoredCylinderMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance infiniteColoredCylinderDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_real_singleton (κ : Type*) [Fintype κ] (M : ℕ) (σ : ColoredPrimeSamples.Sample κ M) :
    (finiteMeasure κ M).real {σ} = (uniformFiniteProbability (ColoredPrimeSamples.Sample κ M)).weight σ := by
  classical
  have hprivate : (Measure.pi (fun _ : κ ↦ finiteRademacherMeasure M)).real {σ.2} =
      ∏ k, (finiteRademacherMeasure M).real {σ.2 k} := by
    change ((Measure.pi (fun _ : κ ↦ finiteRademacherMeasure M)) {σ.2}).toReal = _
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  rw [finiteMeasure, ← Set.singleton_prod_singleton, measureReal_prod_prod, hprivate]
  simp_rw [finiteCylinder_real_singleton]
  simp [cylinderProbability, uniformFiniteProbability, ColoredPrimeSamples.Sample, mul_inv_rev, mul_comm]

theorem finite_weights (κ : Type*) [Fintype κ] (M : ℕ) :
    (finiteProbabilityOfMeasure (finiteMeasure κ M)).weight =
      (uniformFiniteProbability (ColoredPrimeSamples.Sample κ M)).weight := by
  funext σ
  exact finite_real_singleton κ M σ

theorem event (κ : Type*) [Fintype κ] (M : ℕ) (E : ColoredPrimeSamples.Sample κ M → Prop) :
    (measure κ).real {ω | E (restrict κ M ω)} =
      average (fun σ : ColoredPrimeSamples.Sample κ M ↦ if E σ then (1 : ℝ) else 0) := by
  calc
    _ = ((measure κ).map (restrict κ M)).real {σ | E σ} :=
      (map_measureReal_apply (measurable_restrict κ M) MeasurableSet.of_discrete).symm
    _ = _ := by
      rw [map_restrict, ← finiteMeasure_indicator_expectation, finite_weights]

end PaperP1.InfiniteColoredCylinder
