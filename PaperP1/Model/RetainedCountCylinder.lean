module

public import PaperP1.Model.RetainedActiveCount
public import PaperP1.Probability.FiniteObservationLaw

/-! # Exact finite-cylinder realization of the retained-configuration modified count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedCountCylinder

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Model PaperP1.Probability
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations
  PaperP1.MaximumDirectActive PaperP1.RetainedActiveCount

local instance retainedCountCylinderMeasurableF2 : MeasurableSpace F₂ := ⊤
local instance retainedCountCylinderDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def finiteRetained {M : ℕ} (H : ℝ) (N L : ℕ) (G : Finset ℕ) (σ : SampleSpace M) : Prop :=
  RetainedGoodEdges.Retained H N L (activeSites G (fun x ↦ startIndicator x L) σ)

def finiteModified {M : ℕ} (H : ℝ) (N L : ℕ) (G : Finset ℕ) (σ : SampleSpace M) : ℕ :=
  if finiteRetained H N L G σ then indicatorCount G (fun x ↦ startIndicator x L) σ else 0

def badProbability (H : ℝ) (N L : ℕ) (G : Finset ℕ) : ℝ :=
  infiniteRademacherMeasure.real {ω | ¬ retainedActive H N L G ω}

theorem active_restrict {M : ℕ} (G : Finset ℕ) (L : ℕ)
    (hcut : ∀ x ∈ G, x + L ≤ M) (ω : InfiniteSample) :
    activeSites G (fun x ↦ startIndicator x L) (restrictToFinite M ω) = activeSet G L ω := by
  ext x
  simp only [activeSet, activeSites, mem_filter]
  by_cases hx : x ∈ G
  · simp only [hx, true_and, startIndicator_restrict_eq ω (hcut x hx)]
  · simp only [hx, false_and]

theorem finite_retained_restrict {M : ℕ} (H : ℝ) (N L : ℕ) (G : Finset ℕ)
    (hcut : ∀ x ∈ G, x + L ≤ M) (ω : InfiniteSample) :
    finiteRetained H N L G (restrictToFinite M ω) ↔ retainedActive H N L G ω := by
  unfold finiteRetained retainedActive
  rw [active_restrict G L hcut ω]

theorem finite_modified_restrict {M : ℕ} (H : ℝ) (N L : ℕ) (G : Finset ℕ)
    (hcut : ∀ x ∈ G, x + L ≤ M) (ω : InfiniteSample) :
    finiteModified H N L G (restrictToFinite M ω) = modified H N L G ω := by
  unfold finiteModified modified
  rw [finite_retained_restrict H N L G hcut ω]
  split_ifs
  · exact infiniteStartCount_restrict G L M hcut ω
  · rfl

theorem observable_integral (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : ℕ → ℝ) :
    (∫ ω, f (modified H N L G ω) ∂infiniteRademacherMeasure) =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ f (finiteModified H N L G σ)) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  calc
    _ = ∫ ω, f (finiteModified H N L G (restrictToFinite (cutoff G L) ω))
        ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ congrArg f (finite_modified_restrict H N L G hcut ω).symm
    _ = _ := infiniteCylinder_integral (cutoff G L) (fun σ ↦ f (finiteModified H N L G σ))

theorem measurable_modified (H : ℝ) (N L : ℕ) (G : Finset ℕ) : Measurable (modified H N L G) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  have heq : modified H N L G = (finiteModified H N L G) ∘ restrictToFinite (cutoff G L) := by
    funext ω
    exact (finite_modified_restrict H N L G hcut ω).symm
  rw [heq]
  exact Measurable.of_discrete.comp (measurable_restrictToFinite (cutoff G L))

theorem measurable_badEvent (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    MeasurableSet {ω | ¬ retainedActive H N L G ω} := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  have hset : {ω | ¬ retainedActive H N L G ω} =
      restrictToFinite (cutoff G L) ⁻¹' {σ | ¬ finiteRetained H N L G σ} := by
    ext ω
    exact (not_congr (finite_retained_restrict H N L G hcut ω)).symm
  rw [hset]
  exact (measurable_restrictToFinite (cutoff G L)) ((Set.to_countable _).measurableSet)

theorem observable_integrable (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : ℕ → ℝ) :
    Integrable (fun ω ↦ f (modified H N L G ω)) infiniteRademacherMeasure := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  have hi := (integrable_finite_function
    (infiniteRademacherMeasure.map (restrictToFinite (cutoff G L)))
    (fun σ ↦ f (finiteModified H N L G σ))).comp_measurable
      (measurable_restrictToFinite (cutoff G L))
  simpa only [Function.comp_def, finite_modified_restrict H N L G hcut] using hi

theorem event_probability (H : ℝ) (N L : ℕ) (G : Finset ℕ) (E : ℕ → Prop) :
    infiniteRademacherMeasure.real {ω | E (modified H N L G ω)} =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ if E (finiteModified H N L G σ) then 1 else 0) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  rw [← infiniteCylinder_event (cutoff G L) (fun σ ↦ E (finiteModified H N L G σ))]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, finite_modified_restrict H N L G hcut]

theorem original_event_probability (G : Finset ℕ) (L : ℕ) (E : ℕ → Prop) :
    infiniteRademacherMeasure.real {ω | E (infiniteStartCount G L ω)} =
      finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ if E (indicatorCount G (fun x ↦ startIndicator x L) σ) then 1 else 0) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  rw [← infiniteCylinder_event (cutoff G L) (fun σ ↦ E (indicatorCount G (fun x ↦ startIndicator x L) σ))]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, infiniteStartCount_restrict G L (cutoff G L) hcut]

theorem badProbability_eq_disagreement (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    badProbability H N L G = disagreementProbability (cylinderProbability (cutoff G L))
      (finiteModified H N L G) (indicatorCount G (fun x ↦ startIndicator x L)) := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  calc
    _ = infiniteRademacherMeasure.real {ω | modified H N L G ω ≠ infiniteStartCount G L ω} := by
      unfold badProbability
      congr 1
      ext ω
      exact (not_congr (modified_eq_original_iff H N L G ω)).symm
    _ = finiteExpectation (cylinderProbability (cutoff G L)).weight
        (fun σ ↦ if finiteModified H N L G σ ≠ indicatorCount G (fun x ↦ startIndicator x L) σ then 1 else 0) := by
      rw [← infiniteCylinder_event (cutoff G L)
        (fun σ ↦ finiteModified H N L G σ ≠ indicatorCount G (fun x ↦ startIndicator x L) σ)]
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, finite_modified_restrict H N L G hcut,
        infiniteStartCount_restrict G L (cutoff G L) hcut]
    _ = _ := rfl

end PaperP1.RetainedCountCylinder
