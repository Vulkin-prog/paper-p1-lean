module

public import PaperP1.Coding.ProjectionLabelBudget
public import PaperP1.Combinatorics.TargetComponentBudget
public import PaperP1.Combinatorics.LabelClassPartition

/-! # Injective actual target projections force separate component and singleton counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TargetLabelsComponents

open Finset

variable {K U V I : Type*} [Field K] [AddCommGroup U] [Module K U] [Fintype I] [DecidableEq V]

local instance dualDecidableEq : DecidableEq (Module.Dual K U) := Classical.decEq _

theorem projection_labels_eq (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u) :
    ProjectionLabelBudget.labels f = TargetComponentBudget.labels ℓ (univ.image target) := by
  classical
  have hform : ∀ i, ProjectionLabelBudget.form f i = ℓ (target i) := by
    intro i
    ext u
    exact hcoord u i
  ext a
  rw [ProjectionLabelBudget.mem_labels]
  change (a ≠ 0 ∧ ∃ i, ProjectionLabelBudget.form f i = a) ↔
    a ∈ ((univ.image target).image ℓ).erase 0
  constructor
  · rintro ⟨ha, i, hi⟩
    exact mem_erase.mpr ⟨ha, mem_image.mpr ⟨target i, mem_image.mpr ⟨i, mem_univ _, rfl⟩,
      (hform i).symm.trans hi⟩⟩
  · intro ha
    obtain ⟨ha0, haT⟩ := mem_erase.mp ha
    obtain ⟨v, hv, hva⟩ := mem_image.mp haT
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hv
    exact ⟨ha0, i, (hform i).trans hva⟩

theorem labels_le_components (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u)
    (C : Finset (Finset V))
    (hcover : ∀ i, ℓ (target i) ≠ 0 → ∃ D ∈ C, target i ∈ D)
    (hmono : ∀ D ∈ C, ∀ v ∈ D, ∀ w ∈ D, ℓ v = ℓ w) :
    (ProjectionLabelBudget.labels f).card ≤ (TargetComponentBudget.meeting C (univ.image target)).card := by
  rw [projection_labels_eq ℓ f target hcoord]
  apply TargetComponentBudget.labels_le_components ℓ C _ ?_ hmono
  intro v hv hne
  obtain ⟨i, _hi, rfl⟩ := mem_image.mp hv
  exact hcover i hne

variable [FiniteDimensional K U]

theorem projection_rank_le_components (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u)
    (C : Finset (Finset V))
    (hcover : ∀ i, ℓ (target i) ≠ 0 → ∃ D ∈ C, target i ∈ D)
    (hmono : ∀ D ∈ C, ∀ v ∈ D, ∀ w ∈ D, ℓ v = ℓ w) :
    Module.finrank K (LinearMap.range f) ≤ (TargetComponentBudget.meeting C (univ.image target)).card :=
  (ProjectionLabelBudget.rank_le_labels_card f).trans (labels_le_components ℓ f target hcoord C hcover hmono)

theorem injective_dimension_le_components (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u) (hinj : Function.Injective f)
    (C : Finset (Finset V))
    (hcover : ∀ i, ℓ (target i) ≠ 0 → ∃ D ∈ C, target i ∈ D)
    (hmono : ∀ D ∈ C, ∀ v ∈ D, ∀ w ∈ D, ℓ v = ℓ w) :
    Module.finrank K U ≤ (TargetComponentBudget.meeting C (univ.image target)).card := by
  simpa only [LinearMap.finrank_range_of_inj hinj] using
    projection_rank_le_components ℓ f target hcoord C hcover hmono

theorem injective_singleton_budget (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u) (hinj : Function.Injective f)
    (htarget : Function.Injective target) (C : Finset (Finset V))
    (hcover : ∀ i, ℓ (target i) ≠ 0 → ∃ D ∈ C, target i ∈ D)
    (hmono : ∀ D ∈ C, ∀ v ∈ D, ∀ w ∈ D, ℓ v = ℓ w)
    (hdisj : (C : Set (Finset V)).Pairwise Disjoint) :
    2 * Module.finrank K U ≤ Fintype.card I + (TargetComponentBudget.singleton C (univ.image target)).card := by
  have hcomp := injective_dimension_le_components ℓ f target hcoord hinj C hcover hmono
  have hsingle := TargetComponentBudget.singleton_budget C (univ.image target) hdisj
  rw [card_image_of_injective _ htarget, card_univ] at hsingle
  omega

theorem actual_class_budgets [Fintype V] (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u) (hinj : Function.Injective f)
    (htarget : Function.Injective target) :
    Module.finrank K U ≤ (TargetComponentBudget.meeting (LabelClassPartition.parts ℓ) (univ.image target)).card ∧
    2 * Module.finrank K U ≤ Fintype.card I +
      (TargetComponentBudget.singleton (LabelClassPartition.parts ℓ) (univ.image target)).card := by
  have hcover := fun i ↦ LabelClassPartition.covers ℓ (target i)
  have hmono := LabelClassPartition.monochromatic ℓ
  exact ⟨injective_dimension_le_components ℓ f target hcoord hinj _ hcover hmono,
    injective_singleton_budget ℓ f target hcoord hinj htarget _ hcover hmono
      (LabelClassPartition.disjoint_parts ℓ)⟩

omit [FiniteDimensional K U] in
theorem actual_target_class_count [Fintype V] (ℓ : V → Module.Dual K U) (f : U →ₗ[K] (I → K))
    (target : I → V) (hcoord : ∀ u i, f u i = ℓ (target i) u) :
    (TargetComponentBudget.meeting (LabelClassPartition.parts ℓ) (univ.image target)).card =
      (ProjectionLabelBudget.labels f).card := by
  rw [LabelClassPartition.meeting_card, projection_labels_eq ℓ f target hcoord]

end PaperP1.TargetLabelsComponents
