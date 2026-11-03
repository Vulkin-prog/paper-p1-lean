module

public import PaperP1.Arithmetic.TwoTargetSingletonLabels

/-! # A common excluded label set preserves the separate target populations and exact mixed/pure dichotomy -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetAllowedLabels

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports PaperP1.TwoTargetLabelSelection
  PaperP1.TwoTargetSingletonLabels

local instance allowedLabelsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def allowedLabels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) := targetLabels X M j \ E

def allowedSingletons {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) := singletonLabels X M j \ E

theorem mem_allowed_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) (α : Module.Dual F₂ M) :
    α ∈ allowedLabels X M E j ↔ α ≠ 0 ∧
      (targetOffsets (LabelClassPartition.part (label X M) α) j).Nonempty ∧ α ∉ E := by
  simp only [allowedLabels, mem_sdiff, mem_target_labels]
  exact and_assoc

theorem mem_allowed_singletons {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) (α : Module.Dual F₂ M) :
    α ∈ allowedSingletons X M E j ↔ α ≠ 0 ∧
      (targetOffsets (LabelClassPartition.part (label X M) α) j).card = 1 ∧ α ∉ E := by
  simp only [allowedSingletons, mem_sdiff, mem_singleton_labels]
  exact and_assoc

theorem target_population_budget {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) :
    (targetLabels X M j).card ≤ (allowedLabels X M E j).card + E.card := card_le_card_sdiff_add_card

theorem singleton_population_budget {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) :
    (singletonLabels X M j).card ≤ (allowedSingletons X M E j).card + E.card := card_le_card_sdiff_add_card

theorem mixed_or_two_pure {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (k : ℕ)
    (h0 : k + 2 ≤ (allowedLabels X M E 0).card) (h1 : k + 2 ≤ (allowedLabels X M E 1).card) :
    (∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧ (∀ i, α i ∉ E) ∧
      ∀ i : Fin k, ∀ j : Fin 2, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty) ∨
    (∀ j : Fin 2, ∃ α : Fin 2 → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧ (∀ i, α i ∉ E) ∧
      ∀ i : Fin 2, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty ∧
        targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev = ∅) := by
  let mixed := allowedLabels X M E 0 ∩ allowedLabels X M E 1
  by_cases hmix : k ≤ mixed.card
  · obtain ⟨α, hinj, hα⟩ := exists_samples mixed k hmix
    have hdata0 := fun i ↦ (mem_allowed_labels X M E 0 (α i)).mp (mem_inter.mp (hα i)).1
    have hdata1 := fun i ↦ (mem_allowed_labels X M E 1 (α i)).mp (mem_inter.mp (hα i)).2
    refine Or.inl ⟨α, hinj, fun i ↦ (hdata0 i).1, fun i ↦ (hdata0 i).2.2, ?_⟩
    intro i j
    fin_cases j
    · exact (hdata0 i).2.1
    · exact (hdata1 i).2.1
  · apply Or.inr
    have hpure (j : Fin 2) : 2 ≤ (allowedLabels X M E j \ allowedLabels X M E j.rev).card := by
      fin_cases j
      · change 2 ≤ (allowedLabels X M E 0 \ allowedLabels X M E 1).card
        have hsum := card_sdiff_add_card_inter (allowedLabels X M E 0) (allowedLabels X M E 1)
        change _ + mixed.card = _ at hsum
        omega
      · change 2 ≤ (allowedLabels X M E 1 \ allowedLabels X M E 0).card
        have hsum := card_sdiff_add_card_inter (allowedLabels X M E 1) (allowedLabels X M E 0)
        rw [inter_comm] at hsum
        change _ + mixed.card = _ at hsum
        omega
    intro j
    obtain ⟨α, hinj, hα⟩ := exists_samples (allowedLabels X M E j \ allowedLabels X M E j.rev) 2 (hpure j)
    have hallowed := fun i ↦ (mem_allowed_labels X M E j (α i)).mp (mem_sdiff.mp (hα i)).1
    have hpureLabel (i : Fin 2) : α i ∈ pureLabels X M j := by
      refine mem_sdiff.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp (hα i)).1).1, ?_⟩
      intro hother
      exact (mem_sdiff.mp (hα i)).2 (mem_sdiff.mpr ⟨hother, (hallowed i).2.2⟩)
    have hdata := fun i ↦ (mem_pure_labels X M j (α i)).mp (hpureLabel i)
    exact ⟨α, hinj, fun i ↦ (hdata i).1, fun i ↦ (hallowed i).2.2, fun i ↦ (hdata i).2⟩

end PaperP1.TwoTargetAllowedLabels
