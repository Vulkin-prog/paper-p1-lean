module

public import PaperP1.Model.RetainedCountCylinder

/-! # Every observable of the actual finite active set has its literal finite-cylinder integral -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveSetCylinder

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.RetainedActiveCount PaperP1.MaximumDirectActive
  PaperP1.Probability.CylinderExpectations PaperP1.Probability.InfiniteCylinderTransfer

local instance activeSetCylinderMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem observable_integral (G : Finset ℕ) (L : ℕ) (f : Finset ℕ → ℝ) :
    (∫ ω, f (activeSet G L ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ f (activeSites G (fun x ↦ startIndicator x L) σ)) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  calc
    _ = ∫ ω, f (activeSites G (fun x ↦ startIndicator x L) (restrictToFinite (cutoff G L) ω))
        ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg f (RetainedCountCylinder.active_restrict G L hcut ω).symm
    _ = _ := infiniteCylinder_integral (cutoff G L)
      (fun σ ↦ f (activeSites G (fun x ↦ startIndicator x L) σ))

theorem observable_integrable (G : Finset ℕ) (L : ℕ) (f : Finset ℕ → ℝ) :
    Integrable (fun ω ↦ f (activeSet G L ω)) infiniteRademacherMeasure := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  have hi := (integrable_finite_function
    (infiniteRademacherMeasure.map (restrictToFinite (cutoff G L)))
    (fun σ ↦ f (activeSites G (fun x ↦ startIndicator x L) σ))).comp_measurable
      (measurable_restrictToFinite (cutoff G L))
  simpa only [Function.comp_def, RetainedCountCylinder.active_restrict G L hcut] using hi

theorem event_probability (G : Finset ℕ) (L : ℕ) (B : Finset ℕ → Prop) [DecidablePred B] :
    infiniteRademacherMeasure.real {ω | B (activeSet G L ω)} =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ if B (activeSites G (fun x ↦ startIndicator x L) σ) then 1 else 0) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  rw [← infiniteCylinder_event (cutoff G L) (fun σ ↦ B (activeSites G (fun x ↦ startIndicator x L) σ))]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, RetainedCountCylinder.active_restrict G L hcut]

end PaperP1.ActiveSetCylinder
