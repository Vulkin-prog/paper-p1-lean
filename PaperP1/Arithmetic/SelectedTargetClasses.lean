module

public import PaperP1.Arithmetic.ClassPrimeResidual
public import PaperP1.Arithmetic.PhysicalClassData

/-! # Two actual disjoint target classes survive the prime-group selection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedTargetClasses

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations PaperP1.PrimeCircuitSupports
  PaperP1.PrimeCircuitGroups PaperP1.PrimeGroupIncidence PaperP1.WindowPrimeIncidence
  PaperP1.ClassPrimeResidual PaperP1.DisjointRecoveryTheorem

local instance selectedTargetClassesTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance selectedTargetClassesDecEq (W : Type*) : DecidableEq W := Classical.decEq _

theorem mem_targetLabels {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (α : Module.Dual F₂ M) :
    α ∈ DenseTargetRegularization.targetLabels X L M ↔
      α ≠ 0 ∧ ∃ u : Fin (L + 1), label X L M (none, u) = α := by
  rw [ProjectionLabelBudget.mem_labels]
  rfl

theorem physicalClass_disjoint {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) {α β : Module.Dual F₂ M} (hαβ : α ≠ β) :
    Disjoint (physicalClass X M α) (physicalClass X M β) := by
  apply disjoint_left.mpr
  intro v hvα hvβ
  exact hαβ (((mem_physicalClass X M α v).mp hvα).symm.trans ((mem_physicalClass X M β v).mp hvβ))

theorem target_offsets_nonempty {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) {α : Module.Dual F₂ M}
    (hα : α ∈ DenseTargetRegularization.targetLabels X L M) :
    (PhysicalClassData.offsets (physicalClass X M α)).Nonempty := by
  obtain ⟨_, u, hu⟩ := (mem_targetLabels X M α).mp hα
  apply (PhysicalClassData.offsets_nonempty _).mpr
  exact ⟨u, mem_filter.mpr ⟨mem_univ _, (mem_physicalClass X M α _).mpr hu⟩⟩

theorem oldProduct_eq {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (α : Module.Dual F₂ M) :
    oldProduct X M α = PhysicalClassData.sourceProduct (fun a ↦ X (some a)) (physicalClass X M α) := by
  rw [oldProduct, ← PhysicalClassData.source_image]
  rw [prod_image]
  · apply prod_congr rfl
    intro v _
    exact startCompleteVertexLabel_eq_offset (show 0 < X (some v.1) from hX _) v.2
  · intro v _ w _ hvw
    have hfirst : some v.1 = some w.1 := congrArg Prod.fst hvw
    have hsecond : v.2 = w.2 := congrArg (fun q : Option (Fin s) × Fin (L + 1) ↦ q.2) hvw
    exact Prod.ext (Option.some.inj hfirst) hsecond

theorem targetProduct_eq {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (α : Module.Dual F₂ M) :
    ClassPrimeResidual.targetProduct X M α =
      PhysicalClassData.targetProduct (X none) (physicalClass X M α) := by
  rw [ClassPrimeResidual.targetProduct, targetPhysical, ← PhysicalClassData.target_image]
  rw [prod_image]
  · apply prod_congr rfl
    intro u _
    exact startCompleteVertexLabel_eq_offset (show 0 < X none from hX _) u
  · intro v _ w _ hvw
    exact congrArg Prod.snd hvw

theorem exists_two {s L H k : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (A : Finset (Finset (Option (Fin s) × Fin (L + 1))))
    (hA : A ⊆ groups X M H hX hH) (hAk : A.card ≤ k)
    (hlabels : k + 2 ≤ (DenseTargetRegularization.targetLabels X L M).card) :
    ∃ α ∈ DenseTargetRegularization.targetLabels X L M,
      ∃ β ∈ DenseTargetRegularization.targetLabels X L M,
        α ≠ β ∧ α ∉ discarded X M A ∧ β ∉ discarded X M A := by
  have hdiscard := (discarded_card X M hX hH A hA).trans hAk
  have hinter : ((DenseTargetRegularization.targetLabels X L M) ∩ discarded X M A).card ≤
      (discarded X M A).card := card_le_card inter_subset_right
  have hsum := card_sdiff_add_card_inter (DenseTargetRegularization.targetLabels X L M) (discarded X M A)
  have htwo : 1 < (DenseTargetRegularization.targetLabels X L M \ discarded X M A).card := by omega
  obtain ⟨α, hα, β, hβ, hαβ⟩ := one_lt_card.mp htwo
  exact ⟨α, (mem_sdiff.mp hα).1, β, (mem_sdiff.mp hβ).1, hαβ,
    (mem_sdiff.mp hα).2, (mem_sdiff.mp hβ).2⟩

end PaperP1.SelectedTargetClasses
