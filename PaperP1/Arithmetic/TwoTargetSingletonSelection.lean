module

public import PaperP1.Arithmetic.TwoTargetSingletonLabels
public import Mathlib.Combinatorics.Pigeonhole

/-! # Many actual target singletons force a fixed mixed degree-one type or two pure classes in each target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetSingletonSelection

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetLabelSelection PaperP1.TwoTargetSingletonLabels

local instance singletonSelectionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def mixedSingletons {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) (j : Fin 2) :=
  singletonLabels X M j ∩ targetLabels X M j.rev

theorem mixed_type_samples {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (K k : ℕ) (hk : 1 ≤ k)
    (hsize : ∀ α : Module.Dual F₂ M, α ≠ 0 → (LabelClassPartition.part (label X M) α).card ≤ K)
    (j : Fin 2) (hmany : (K + 1) * k ≤ (mixedSingletons X M j).card) :
    ∃ a : ℕ, 0 < a ∧ ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev).card = a ∧
        (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).card = 1 := by
  let S := mixedSingletons X M j
  let degree := fun α : Module.Dual F₂ M ↦ (targetOffsets (LabelClassPartition.part (label X M) α) j.rev).card
  have hmaps : ∀ α ∈ S, degree α ∈ range (K + 1) := by
    intro α hα
    have hα0 := ((mem_singleton_labels X M j α).mp (mem_inter.mp hα).1).1
    have hle : degree α ≤ K := by
      dsimp only [degree]
      rw [target_offsets_card, target_indices_card]
      exact (card_le_card inter_subset_left).trans (hsize α hα0)
    exact mem_range.mpr (by omega)
  obtain ⟨a, _ha, hcard⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := S) (t := range (K + 1)) (f := degree) hmaps ⟨0, mem_range.mpr (by omega)⟩
    (by simpa only [card_range] using hmany)
  obtain ⟨α, hinj, hα⟩ := exists_samples (S.filter fun α ↦ degree α = a) k hcard
  have hdata (i : Fin k) := (mem_singleton_labels X M j (α i)).mp
    (mem_inter.mp (mem_filter.mp (hα i)).1).1
  have hdegree (i : Fin k) : degree (α i) = a := (mem_filter.mp (hα i)).2
  have ha : 0 < a := by
    let i : Fin k := ⟨0, by omega⟩
    have hne := ((mem_target_labels X M j.rev (α i)).mp
      (mem_inter.mp (mem_filter.mp (hα i)).1).2).2
    have hpos : 0 < degree (α i) := hne.card_pos
    rwa [hdegree i] at hpos
  exact ⟨a, ha, α, hinj, fun i ↦ (hdata i).1, fun i ↦ ⟨hdegree i, (hdata i).2⟩⟩

theorem singleton_dichotomy {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (K k : ℕ) (hk : 1 ≤ k)
    (hsize : ∀ α : Module.Dual F₂ M, α ≠ 0 → (LabelClassPartition.part (label X M) α).card ≤ K)
    (hmany : ∀ j : Fin 2, (K + 1) * k + 2 ≤ (singletonLabels X M j).card) :
    (∃ j : Fin 2, ∃ a : ℕ, 0 < a ∧ ∃ α : Fin k → Module.Dual F₂ M,
      Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev).card = a ∧
        (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).card = 1) ∨
    (∀ j : Fin 2, ∃ α : Fin 2 → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
      ∀ i : Fin 2, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty ∧
        targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev = ∅) := by
  classical
  by_cases hmixed : ∃ j : Fin 2, (K + 1) * k ≤ (mixedSingletons X M j).card
  · obtain ⟨j, hj⟩ := hmixed
    exact Or.inl ⟨j, mixed_type_samples X M K k hk hsize j hj⟩
  · apply Or.inr
    intro j
    have hpure : 2 ≤ (singletonLabels X M j \ targetLabels X M j.rev).card := by
      have hsum := card_sdiff_add_card_inter (singletonLabels X M j) (targetLabels X M j.rev)
      change _ + (mixedSingletons X M j).card = _ at hsum
      have hsmall : ¬ (K + 1) * k ≤ (mixedSingletons X M j).card := fun h ↦ hmixed ⟨j, h⟩
      have hlarge := hmany j
      omega
    obtain ⟨α, hinj, hα⟩ := exists_samples (singletonLabels X M j \ targetLabels X M j.rev) 2 hpure
    have hdata (i : Fin 2) : α i ∈ pureLabels X M j :=
      mem_sdiff.mpr ⟨(mem_filter.mp (mem_sdiff.mp (hα i)).1).1, (mem_sdiff.mp (hα i)).2⟩
    have h := fun i ↦ (mem_pure_labels X M j (α i)).mp (hdata i)
    exact ⟨α, hinj, fun i ↦ (h i).1, fun i ↦ (h i).2⟩

end PaperP1.TwoTargetSingletonSelection
