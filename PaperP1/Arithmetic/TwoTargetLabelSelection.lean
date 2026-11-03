module

public import PaperP1.Arithmetic.TwoTargetClassOffsets
public import Mathlib.Data.Fintype.EquivFin

/-! # Separate target label populations force either many mixed classes or two pure classes per target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetLabelSelection

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports

local instance labelSelectionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def targetLabels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) (j : Fin 2) :=
  TargetComponentBudget.labels (label X M)
    (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L))

def mixedLabels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) :=
  targetLabels X M 0 ∩ targetLabels X M 1

def pureLabels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) (j : Fin 2) :=
  targetLabels X M j \ targetLabels X M j.rev

theorem mem_target_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (j : Fin 2) (α : Module.Dual F₂ M) : α ∈ targetLabels X M j ↔
      α ≠ 0 ∧ (targetOffsets (LabelClassPartition.part (label X M) α) j).Nonempty := by
  rw [offsets_nonempty_iff]
  constructor
  · intro hα
    obtain ⟨hα0, v, hvT, hvα⟩ := mem_erase.mp hα |>.imp_right mem_image.mp
    exact ⟨hα0, v, mem_inter.mpr ⟨(LabelClassPartition.mem_part _ _ _).mpr hvα, hvT⟩⟩
  · rintro ⟨hα0, v, hv⟩
    obtain ⟨hvD, hvT⟩ := mem_inter.mp hv
    exact mem_erase.mpr ⟨hα0, mem_image.mpr ⟨v, hvT, (LabelClassPartition.mem_part _ _ _).mp hvD⟩⟩

theorem mem_mixed_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : α ∈ mixedLabels X M ↔
      α ≠ 0 ∧ ∀ j : Fin 2, (targetOffsets (LabelClassPartition.part (label X M) α) j).Nonempty := by
  simp only [mixedLabels, mem_inter, mem_target_labels]
  constructor
  · rintro ⟨⟨hα0, h0⟩, _hα0, h1⟩
    refine ⟨hα0, ?_⟩
    intro j
    fin_cases j <;> assumption
  · rintro ⟨hα0, hall⟩
    exact ⟨⟨hα0, hall 0⟩, hα0, hall 1⟩

theorem mem_pure_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (j : Fin 2) (α : Module.Dual F₂ M) : α ∈ pureLabels X M j ↔
      α ≠ 0 ∧ (targetOffsets (LabelClassPartition.part (label X M) α) j).Nonempty ∧
        targetOffsets (LabelClassPartition.part (label X M) α) j.rev = ∅ := by
  rw [pureLabels, mem_sdiff, mem_target_labels, mem_target_labels]
  constructor
  · rintro ⟨⟨hα0, hne⟩, hnot⟩
    exact ⟨hα0, hne, not_nonempty_iff_eq_empty.mp (fun h ↦ hnot ⟨hα0, h⟩)⟩
  · rintro ⟨hα0, hne, hempty⟩
    refine ⟨⟨hα0, hne⟩, ?_⟩
    rintro ⟨_, hother⟩
    rw [hempty] at hother
    exact not_nonempty_empty hother

theorem exists_samples {A : Type*} [DecidableEq A] (S : Finset A) (k : ℕ) (hk : k ≤ S.card) :
    ∃ f : Fin k → A, Function.Injective f ∧ ∀ i, f i ∈ S := by
  let e : Fin k → S := fun i ↦ S.equivFin.symm (Fin.castLE hk i)
  refine ⟨fun i ↦ (e i).val, ?_, fun i ↦ (e i).property⟩
  exact Subtype.val_injective.comp (S.equivFin.symm.injective.comp (Fin.castLE_injective hk))

theorem mixed_or_two_pure {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (k : ℕ) (h0 : k + 2 ≤ (targetLabels X M 0).card) (h1 : k + 2 ≤ (targetLabels X M 1).card) :
    (∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i : Fin k, ∀ j : Fin 2,
        (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty) ∨
    (∀ j : Fin 2, ∃ α : Fin 2 → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i : Fin 2, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty ∧
        targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev = ∅) := by
  by_cases hmix : k ≤ (mixedLabels X M).card
  · obtain ⟨α, hinj, hα⟩ := exists_samples (mixedLabels X M) k hmix
    have hdata := fun i ↦ (mem_mixed_labels X M (α i)).mp (hα i)
    exact Or.inl ⟨α, hinj, fun i ↦ (hdata i).1, fun i ↦ (hdata i).2⟩
  · apply Or.inr
    have hpure (j : Fin 2) : 2 ≤ (pureLabels X M j).card := by
      fin_cases j
      · change 2 ≤ (targetLabels X M 0 \ targetLabels X M 1).card
        have hsum := card_sdiff_add_card_inter (targetLabels X M 0) (targetLabels X M 1)
        change _ + (mixedLabels X M).card = _ at hsum
        omega
      · change 2 ≤ (targetLabels X M 1 \ targetLabels X M 0).card
        have hsum := card_sdiff_add_card_inter (targetLabels X M 1) (targetLabels X M 0)
        rw [inter_comm] at hsum
        change _ + (mixedLabels X M).card = _ at hsum
        omega
    intro j
    obtain ⟨α, hinj, hα⟩ := exists_samples (pureLabels X M j) 2 (hpure j)
    have hdata := fun i ↦ (mem_pure_labels X M j (α i)).mp (hα i)
    exact ⟨α, hinj, fun i ↦ (hdata i).1, fun i ↦ (hdata i).2⟩

end PaperP1.TwoTargetLabelSelection
