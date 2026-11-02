module

public import PaperP1.Model.RetainedCountCylinder
public import PaperP1.Probability.FiniteMomentTransfer

/-! # Actual original-to-retained moment transfer with an explicit truncation error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedMomentTransfer

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Model PaperP1.Probability
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.CountObservables
  PaperP1.MaximumDirectActive PaperP1.RetainedCountCylinder PaperP1.RetainedActiveCount
  PaperP1.Probability.CylinderExpectations PaperP1.Probability.InfiniteCylinderTransfer

local instance retainedMomentTransferMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance retainedMomentTransferDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def modifiedMoment (H : ℝ) (N L : ℕ) (G : Finset ℕ) (j : ℕ) : ℝ :=
  ∫ ω, (modified H N L G ω : ℝ) ^ j ∂infiniteRademacherMeasure

theorem original_observable_integral (G : Finset ℕ) (L : ℕ) (f : ℕ → ℝ) :
    (∫ ω, f (infiniteStartCount G L ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ f (indicatorCount G (fun x ↦ startIndicator x L) σ)) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  calc
    _ = ∫ ω, f (indicatorCount G (fun x ↦ startIndicator x L)
        (restrictToFinite (cutoff G L) ω)) ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg f (infiniteStartCount_restrict G L _ hcut ω).symm
    _ = _ := infiniteCylinder_integral (cutoff G L)
      (fun σ ↦ f (indicatorCount G (fun x ↦ startIndicator x L) σ))

theorem original_observable_integrable (G : Finset ℕ) (L : ℕ) (f : ℕ → ℝ) :
    Integrable (fun ω ↦ f (infiniteStartCount G L ω)) infiniteRademacherMeasure := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  have hi := (integrable_finite_function
    (infiniteRademacherMeasure.map (restrictToFinite (cutoff G L)))
    (fun σ ↦ f (indicatorCount G (fun x ↦ startIndicator x L) σ))).comp_measurable
      (measurable_restrictToFinite (cutoff G L))
  simpa only [Function.comp_def, infiniteStartCount_restrict G L (cutoff G L) hcut] using hi

theorem finite_modified_le {M : ℕ} (H : ℝ) (N L : ℕ) (G : Finset ℕ) (σ : SampleSpace M) :
    finiteModified H N L G σ ≤ indicatorCount G (fun x ↦ startIndicator x L) σ := by
  unfold finiteModified
  split_ifs <;> omega

theorem original_disagreement (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    disagreementProbability (cylinderProbability (cutoff G L))
      (indicatorCount G (fun x ↦ startIndicator x L)) (finiteModified H N L G) = badProbability H N L G := by
  rw [badProbability_eq_disagreement]
  unfold disagreementProbability
  simp only [ne_comm]

theorem moment_truncation (H : ℝ) (N L : ℕ) (G : Finset ℕ)
    (j q : ℕ) (hjq : j ≤ q) (R : ℝ) (hR : 0 < R) :
    |countMoment G L j - modifiedMoment H N L G j| ≤
      R ^ j * badProbability H N L G + countMoment G L q / R ^ (q - j) := by
  simp only [countMoment, modifiedMoment]
  rw [original_observable_integral G L (fun n ↦ (n : ℝ) ^ j),
    RetainedCountCylinder.observable_integral H N L G (fun n ↦ (n : ℝ) ^ j),
    original_observable_integral G L (fun n ↦ (n : ℝ) ^ q)]
  have h := ordered_moment_difference_bound (cylinderProbability (cutoff G L))
    (indicatorCount G (fun x ↦ startIndicator x L)) (finiteModified H N L G)
    (finite_modified_le H N L G) j q hjq R hR
  rw [original_disagreement] at h
  exact h

end PaperP1.RetainedMomentTransfer
