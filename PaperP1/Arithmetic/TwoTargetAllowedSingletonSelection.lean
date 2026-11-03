module

public import PaperP1.Arithmetic.TwoTargetAllowedLabels
public import Mathlib.Combinatorics.Pigeonhole

/-! # Fixed-degree singleton samples outside a common excluded label set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetAllowedSingletonSelection

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports PaperP1.TwoTargetLabelSelection
  PaperP1.TwoTargetSingletonLabels PaperP1.TwoTargetAllowedLabels

local instance allowedSingletonPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem fixed_degree_samples {A : Type*} [DecidableEq A] (S : Finset A) (degree : A → ℕ)
    (K k : ℕ) (hk : 1 ≤ k) (hdegree : ∀ α ∈ S, 0 < degree α ∧ degree α ≤ K)
    (hmany : (K + 1) * k ≤ S.card) :
    ∃ a : ℕ, 0 < a ∧ ∃ α : Fin k → A, Function.Injective α ∧
      ∀ i, α i ∈ S ∧ degree (α i) = a := by
  have hmaps : ∀ α ∈ S, degree α ∈ range (K + 1) := by
    intro α hα
    exact mem_range.mpr (by have h := (hdegree α hα).2; omega)
  obtain ⟨a, _ha, hcard⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := S) (t := range (K + 1)) (f := degree) hmaps ⟨0, mem_range.mpr (by omega)⟩
    (by simpa only [card_range] using hmany)
  obtain ⟨α, hinj, hα⟩ := exists_samples (S.filter fun α ↦ degree α = a) k hcard
  have hdata (i : Fin k) : α i ∈ S ∧ degree (α i) = a := mem_filter.mp (hα i)
  have ha : 0 < a := by
    let i : Fin k := ⟨0, by omega⟩
    have hpos := (hdegree (α i) (hdata i).1).1
    rwa [(hdata i).2] at hpos
  exact ⟨a, ha, α, hinj, hdata⟩

def mixedSingletons {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (j : Fin 2) :=
  allowedSingletons X M E j ∩ targetLabels X M j.rev

theorem mixed_type_samples {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (K k : ℕ) (hk : 1 ≤ k)
    (hsize : ∀ α : Module.Dual F₂ M, α ≠ 0 → (LabelClassPartition.part (label X M) α).card ≤ K)
    (j : Fin 2) (hmany : (K + 1) * k ≤ (mixedSingletons X M E j).card) :
    ∃ a : ℕ, 0 < a ∧ ∃ α : Fin k → Module.Dual F₂ M, Function.Injective α ∧
      (∀ i, α i ≠ 0) ∧ (∀ i, α i ∉ E) ∧
      ∀ i, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev).card = a ∧
        (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).card = 1 := by
  let S := mixedSingletons X M E j
  let degree := fun α : Module.Dual F₂ M ↦ (targetOffsets (LabelClassPartition.part (label X M) α) j.rev).card
  have hdegree : ∀ α ∈ S, 0 < degree α ∧ degree α ≤ K := by
    intro α hα
    have hd := (mem_allowed_singletons X M E j α).mp (mem_inter.mp hα).1
    refine ⟨((mem_target_labels X M j.rev α).mp (mem_inter.mp hα).2).2.card_pos, ?_⟩
    dsimp only [degree]
    rw [target_offsets_card, target_indices_card]
    exact (card_le_card inter_subset_left).trans (hsize α hd.1)
  obtain ⟨a, ha, α, hinj, hα⟩ := fixed_degree_samples S degree K k hk hdegree hmany
  have hdata (i : Fin k) := (mem_allowed_singletons X M E j (α i)).mp (mem_inter.mp (hα i).1).1
  exact ⟨a, ha, α, hinj, fun i ↦ (hdata i).1, fun i ↦ (hdata i).2.2,
    fun i ↦ ⟨(hα i).2, (hdata i).2.1⟩⟩

theorem singleton_dichotomy {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (E : Finset (Module.Dual F₂ M)) (K k : ℕ) (hk : 1 ≤ k)
    (hsize : ∀ α : Module.Dual F₂ M, α ≠ 0 → (LabelClassPartition.part (label X M) α).card ≤ K)
    (hmany : ∀ j : Fin 2, (K + 1) * k + 2 ≤ (allowedSingletons X M E j).card) :
    (∃ j : Fin 2, ∃ a : ℕ, 0 < a ∧ ∃ α : Fin k → Module.Dual F₂ M,
      Function.Injective α ∧ (∀ i, α i ≠ 0) ∧ (∀ i, α i ∉ E) ∧
      ∀ i, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev).card = a ∧
        (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).card = 1) ∨
    (∀ j : Fin 2, ∃ α : Fin 2 → Module.Dual F₂ M, Function.Injective α ∧
      (∀ i, α i ≠ 0) ∧ (∀ i, α i ∉ E) ∧
      ∀ i : Fin 2, (targetOffsets (LabelClassPartition.part (label X M) (α i)) j).Nonempty ∧
        targetOffsets (LabelClassPartition.part (label X M) (α i)) j.rev = ∅) := by
  by_cases hmixed : ∃ j : Fin 2, (K + 1) * k ≤ (mixedSingletons X M E j).card
  · obtain ⟨j, hj⟩ := hmixed
    exact Or.inl ⟨j, mixed_type_samples X M E K k hk hsize j hj⟩
  · apply Or.inr
    intro j
    have hpure : 2 ≤ (allowedSingletons X M E j \ targetLabels X M j.rev).card := by
      have hsum := card_sdiff_add_card_inter (allowedSingletons X M E j) (targetLabels X M j.rev)
      change _ + (mixedSingletons X M E j).card = _ at hsum
      have hsmall : ¬ (K + 1) * k ≤ (mixedSingletons X M E j).card := fun h ↦ hmixed ⟨j, h⟩
      have hlarge := hmany j
      omega
    obtain ⟨α, hinj, hα⟩ := exists_samples (allowedSingletons X M E j \ targetLabels X M j.rev) 2 hpure
    have hallowed (i : Fin 2) := (mem_allowed_singletons X M E j (α i)).mp (mem_sdiff.mp (hα i)).1
    have hpureLabel (i : Fin 2) : α i ∈ pureLabels X M j := by
      refine mem_sdiff.mpr ⟨?_, (mem_sdiff.mp (hα i)).2⟩
      exact (mem_filter.mp (mem_sdiff.mp (mem_sdiff.mp (hα i)).1).1).1
    have hdata := fun i ↦ (mem_pure_labels X M j (α i)).mp (hpureLabel i)
    exact ⟨α, hinj, fun i ↦ (hdata i).1, fun i ↦ (hallowed i).2.2, fun i ↦ (hdata i).2⟩

end PaperP1.TwoTargetAllowedSingletonSelection
