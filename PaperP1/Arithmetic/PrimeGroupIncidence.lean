module

public import PaperP1.Arithmetic.PrimeCircuitGroups

/-! # A fixed bound for the actual prime groups incident to a label class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeGroupIncidence

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations PaperP1.PrimeCircuitSupports
  PaperP1.PrimeCircuitGroups PaperP1.DisjointRecoveryTheorem PaperP1.PhysicalLabelSupportCount

local instance primeGroupIncidenceTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance primeGroupIncidenceDecEq (W : Type*) : DecidableEq W := Classical.decEq _

def physicalClass {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : Finset (Option (Fin s) × Fin (L + 1)) :=
  univ.filter fun v ↦ label X L M v = α

theorem mem_physicalClass {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (α : Module.Dual F₂ M)
    (v : Option (Fin s) × Fin (L + 1)) : v ∈ physicalClass X M α ↔ label X L M v = α := by
  simp only [physicalClass, mem_filter, mem_univ, true_and]

theorem physicalClass_card {s L t : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L))
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    {α : Module.Dual F₂ M} (hα : α ≠ 0) : (physicalClass X M α).card ≤ t - 1 :=
  hM.2.2.1 α hα

def targetSupportLabels {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (F : Finset (Option (Fin s) × Fin (L + 1))) :
    Finset (Module.Dual F₂ M) := (F.filter fun v ↦ v.1 = none).image (label X L M)

theorem targetSupportLabels_singleton {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    {F : Finset (Option (Fin s) × Fin (L + 1))} (hF : F ∈ groups X M H hX hH) :
    ∃ u : Fin (L + 1), (none, u) ∈ F ∧ label X L M (none, u) ≠ 0 ∧
      F ∈ throughPool X L M (none, u) ∧
      targetSupportLabels X M F = {label X L M (none, u)} := by
  obtain ⟨u, hu, hactive, hpool, hunique, _⟩ := group_target_source X M hX hH hF
  refine ⟨u, hu, hactive, hpool, ?_⟩
  ext β
  constructor
  · intro hβ
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hβ
    obtain ⟨hv, hi⟩ := mem_filter.mp hv
    rw [hunique v hv hi]
    exact mem_singleton_self _
  · intro hβ
    rw [mem_singleton.mp hβ]
    exact mem_image.mpr ⟨(none, u), mem_filter.mpr ⟨hu, rfl⟩, rfl⟩

def incident {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (α : Module.Dual F₂ M) :=
  (groups X M H hX hH).filter fun F ↦ α ∈ targetSupportLabels X M F

theorem incident_cover {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (α : Module.Dual F₂ M) :
    incident X M H hX hH α ⊆ (physicalClass X M α).biUnion (throughPool X L M) := by
  intro F hF
  obtain ⟨hF, hα⟩ := mem_filter.mp hF
  obtain ⟨u, _, _, hpool, hlabels⟩ := targetSupportLabels_singleton X M hX hH hF
  rw [hlabels] at hα
  exact mem_biUnion.mpr ⟨(none, u),
    (mem_physicalClass X M α _).mpr (mem_singleton.mp hα).symm, hpool⟩

theorem incident_card {s L H t : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (ht : 2 ≤ t)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    {α : Module.Dual F₂ M} (hα : α ≠ 0) :
    (incident X M H hX hH α).card ≤ (t - 1) * supportBound s t (t - 1) := by
  calc
    _ ≤ ((physicalClass X M α).biUnion (throughPool X L M)).card :=
      card_le_card (incident_cover X M hX hH α)
    _ ≤ ∑ v ∈ physicalClass X M α, (throughPool X L M v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ physicalClass X M α, supportBound s t (t - 1) := by
      apply sum_le_sum
      intro v hv
      apply throughPool_card X M t ht hM v
      rw [(mem_physicalClass X M α v).mp hv]
      exact hα
    _ = (physicalClass X M α).card * supportBound s t (t - 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (physicalClass_card X M hM hα)

def discarded {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (A : Finset (Finset (Option (Fin s) × Fin (L + 1)))) := A.biUnion (targetSupportLabels X M)

theorem discarded_card {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (A : Finset (Finset (Option (Fin s) × Fin (L + 1)))) (hA : A ⊆ groups X M H hX hH) :
    (discarded X M A).card ≤ A.card := by
  calc
    _ ≤ ∑ F ∈ A, (targetSupportLabels X M F).card := card_biUnion_le
    _ = A.card := by
      have heq : ∀ F ∈ A, (targetSupportLabels X M F).card = 1 := by
        intro F hF
        obtain ⟨u, _, _, _, hlabels⟩ := targetSupportLabels_singleton X M hX hH (hA hF)
        rw [hlabels, card_singleton]
      simp only [sum_congr rfl heq, sum_const, smul_eq_mul, mul_one]

theorem incident_outside_selected {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (A : Finset (Finset (Option (Fin s) × Fin (L + 1))))
    {α : Module.Dual F₂ M} (hα : α ∉ discarded X M A)
    {F : Finset (Option (Fin s) × Fin (L + 1))} (hF : F ∈ incident X M H hX hH α) :
    F ∈ groups X M H hX hH \ A := by
  obtain ⟨hFG, hFα⟩ := mem_filter.mp hF
  exact mem_sdiff.mpr ⟨hFG, fun hFA ↦ hα (mem_biUnion.mpr ⟨F, hFA, hFα⟩)⟩

end PaperP1.PrimeGroupIncidence
