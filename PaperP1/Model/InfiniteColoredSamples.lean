module

public import PaperP1.Model.ColoredPrimeSamples
public import PaperP1.Probability.CylinderExpectations
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Infinite colored prime-sign replicas and their exact finite cylinder law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteColoredSamples

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance infiniteColoredSamplesMeasurableF2 : MeasurableSpace F₂ := ⊤

abbrev Sample (κ : Type*) := InfiniteSample × (κ → InfiniteSample)

def measure (κ : Type*) [Fintype κ] : Measure (Sample κ) :=
  infiniteRademacherMeasure.prod (Measure.pi (fun _ : κ ↦ infiniteRademacherMeasure))

instance isProbability (κ : Type*) [Fintype κ] : IsProbabilityMeasure (measure κ) := by
  unfold measure
  infer_instance

def restrict (κ : Type*) (M : ℕ) (ω : Sample κ) : ColoredPrimeSamples.Sample κ M :=
  (restrictToFinite M ω.1, fun k ↦ restrictToFinite M (ω.2 k))

theorem measurable_restrict (κ : Type*) (M : ℕ) : Measurable (restrict κ M) := by
  exact ((measurable_restrictToFinite M).comp measurable_fst).prodMk
    (Measurable.of_eval (fun k ↦ (measurable_restrictToFinite M).comp ((measurable_pi_apply k).comp measurable_snd)))

def finiteMeasure (κ : Type*) [Fintype κ] (M : ℕ) : Measure (ColoredPrimeSamples.Sample κ M) :=
  (finiteRademacherMeasure M).prod (Measure.pi (fun _ : κ ↦ finiteRademacherMeasure M))

instance finiteIsProbability (κ : Type*) [Fintype κ] (M : ℕ) : IsProbabilityMeasure (finiteMeasure κ M) := by
  unfold finiteMeasure
  infer_instance

theorem map_restrict (κ : Type*) [Fintype κ] (M : ℕ) :
    (measure κ).map (restrict κ M) = finiteMeasure κ M := by
  have hprivate : (Measure.pi (fun _ : κ ↦ infiniteRademacherMeasure)).map
      (fun ω k ↦ restrictToFinite M (ω k)) = Measure.pi (fun _ : κ ↦ finiteRademacherMeasure M) := by
    rw [Measure.pi_map_pi (fun _ ↦ (measurable_restrictToFinite M).aemeasurable)]
    simp_rw [map_infiniteRademacherMeasure_restrictToFinite]
  have hprod := Measure.map_prod_map infiniteRademacherMeasure
    (Measure.pi (fun _ : κ ↦ infiniteRademacherMeasure)) (measurable_restrictToFinite M)
    (Measurable.of_eval (fun k ↦ (measurable_restrictToFinite M).comp (measurable_pi_apply k)))
  change (infiniteRademacherMeasure.map (restrictToFinite M)).prod
      ((Measure.pi (fun _ : κ ↦ infiniteRademacherMeasure)).map (fun ω k ↦ restrictToFinite M (ω k))) =
      (measure κ).map (restrict κ M) at hprod
  rw [map_infiniteRademacherMeasure_restrictToFinite, hprivate] at hprod
  exact hprod.symm

end PaperP1.InfiniteColoredSamples
