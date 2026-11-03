module

public import PaperP1.Arithmetic.TwoTargetLabelDimension

/-! # Actual target singleton classes are counted by their distinct nonzero labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetSingletonLabels

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetLabelSelection

local instance singletonLabelsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def singletonLabels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) (j : Fin 2) :=
  (targetLabels X M j).filter fun α ↦ (targetOffsets (LabelClassPartition.part (label X M) α) j).card = 1

theorem mem_singleton_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (j : Fin 2) (α : Module.Dual F₂ M) : α ∈ singletonLabels X M j ↔
      α ≠ 0 ∧ (targetOffsets (LabelClassPartition.part (label X M) α) j).card = 1 := by
  rw [singletonLabels, mem_filter, mem_target_labels]
  constructor
  · rintro ⟨⟨hα, _hne⟩, hc⟩
    exact ⟨hα, hc⟩
  · rintro ⟨hα, hc⟩
    exact ⟨⟨hα, card_pos.mp (by omega)⟩, hc⟩

theorem singleton_parts_eq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) (j : Fin 2) :
    TargetComponentBudget.singleton (LabelClassPartition.parts (label X M))
      (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L)) =
      (singletonLabels X M j).image (LabelClassPartition.part (label X M)) := by
  let T := univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L)
  ext D
  constructor
  · intro hD
    obtain ⟨hpart, hcard⟩ := mem_filter.mp hD
    have hcard' : (D ∩ T).card = 1 := hcard
    have hmeet : D ∈ TargetComponentBudget.meeting (LabelClassPartition.parts (label X M)) T :=
      mem_filter.mpr ⟨hpart, card_pos.mp (by omega)⟩
    rw [LabelClassPartition.meeting_eq_image] at hmeet
    obtain ⟨α, hα, rfl⟩ := mem_image.mp hmeet
    have hcount : (targetOffsets (LabelClassPartition.part (label X M) α) j).card = 1 := by
      rw [target_offsets_card, target_indices_card]
      exact hcard
    exact mem_image.mpr ⟨α, mem_filter.mpr ⟨hα, hcount⟩, rfl⟩
  · intro hD
    obtain ⟨α, hα, rfl⟩ := mem_image.mp hD
    obtain ⟨hαT, hc⟩ := mem_filter.mp hα
    have hmeet : LabelClassPartition.part (label X M) α ∈
        TargetComponentBudget.meeting (LabelClassPartition.parts (label X M)) T := by
      rw [LabelClassPartition.meeting_eq_image]
      exact mem_image.mpr ⟨α, hαT, rfl⟩
    rw [target_offsets_card, target_indices_card] at hc
    exact mem_filter.mpr ⟨(mem_filter.mp hmeet).1, hc⟩

theorem singleton_labels_card {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) (j : Fin 2) :
    (singletonLabels X M j).card =
      (TargetComponentBudget.singleton (LabelClassPartition.parts (label X M))
        (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L))).card := by
  rw [singleton_parts_eq]
  symm
  apply card_image_iff.mpr
  intro α hα β _hβ hab
  have hαT := (mem_filter.mp hα).1
  obtain ⟨_hα0, v, _hvT, hvα⟩ := mem_erase.mp hαT |>.imp_right mem_image.mp
  have hvD : v ∈ LabelClassPartition.part (label X M) α := (LabelClassPartition.mem_part _ _ _).mpr hvα
  have hvE : v ∈ LabelClassPartition.part (label X M) β := hab ▸ hvD
  exact hvα.symm.trans ((LabelClassPartition.mem_part _ _ _).mp hvE)

theorem dimension_singleton_budget {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L))
    (hinj : ∀ j : Fin 2, Function.Injective ((projection X L (Sum.inr j)).comp P.subtype)) (j : Fin 2) :
    2 * Module.finrank F₂ P ≤ L + 1 + (singletonLabels X P j).card := by
  have h := (TwoTargetPhysicalBudgets.class_budgets X P hinj j).2
  exact h.trans_eq (congrArg (Nat.add (L + 1)) (singleton_labels_card X P j).symm)

end PaperP1.TwoTargetSingletonLabels
