module

public import PaperP1.Arithmetic.OneTargetPhysicalLift
public import PaperP1.Arithmetic.TwoTargetLabelDimension

/-! # One actual dense intersection retains many physical classes while the auxiliary target stays identically zero -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneTargetPhysicalRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections
  PaperP1.PhysicalWindowRelations PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.DisjointRecoverySubspace

local instance oneTargetRegularizationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance intersectionAddCommGroup {y L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup ↥(W ⊓ squareClassSpace y L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ℕ →₀ F₂) (W ⊓ squareClassSpace y L)
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ P) := Classical.decEq _

theorem dimension_le_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (P : Submodule F₂ (code X L))
    (j : Fin 2) (hinj : Function.Injective ((projection X L (Sum.inr j)).comp P.subtype)) :
    Module.finrank F₂ P ≤ (TwoTargetLabelSelection.targetLabels X P j).card := by
  let ℓ := label X P
  have hcoord : ∀ r : P, ∀ i : Fin (L + 1),
      ((projection X L (Sum.inr j)).comp P.subtype) r i = ℓ (Sum.inr j, i) r := fun _ _ ↦ rfl
  have htarget : Function.Injective (fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L)) :=
    fun _ _ h ↦ (Prod.mk.inj h).2
  have h := (TargetLabelsComponents.actual_class_budgets ℓ
    ((projection X L (Sum.inr j)).comp P.subtype) (fun i ↦ ((Sum.inr j, i) : Coordinate s L))
    hcoord hinj htarget).1
  have heq := LabelClassPartition.meeting_card ℓ
    (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))
  have h' : Module.finrank F₂ P ≤ (TargetComponentBudget.meeting (LabelClassPartition.parts ℓ)
      (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card := by
    simpa only [Fintype.card_fin] using h
  exact h'.trans_eq heq

theorem zero_projection_offsets {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (P : Submodule F₂ (code X L))
    (j : Fin 2) (hzero : (projection X L (Sum.inr j)).comp P.subtype = 0)
    (α : Module.Dual F₂ P) (hα : α ≠ 0) :
    targetOffsets (LabelClassPartition.part (label X P) α) j = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨i, hi, _hiw⟩ := mem_image.mp hw
  have hlabel := (LabelClassPartition.mem_part _ _ _).mp (mem_filter.mp hi).2
  have hz : label X P (Sum.inr j, i) = 0 := by
    ext u
    exact congrFun (LinearMap.congr_fun hzero u) i
  exact hα (hlabel.symm.trans hz)

theorem uniform_subspace (s : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ x : Fin s → ℕ, ∀ y z L : ℕ, 1 ≤ L →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      ∃ P : Submodule F₂ (code (starts x y z) L),
        NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t ∧
        (Module.finrank F₂ ↥(W ⊓ squareClassSpace y L) : ℝ) - ξ * L / 4 ≤ Module.finrank F₂ P ∧
        Function.Injective ((projection (starts x y z) L (Sum.inr 0)).comp P.subtype) ∧
        (projection (starts x y z) L (Sum.inr 1)).comp P.subtype = 0 := by
  obtain ⟨t, ht, hcost⟩ := SmallRecoveryParameter.exists_relative_cost (s + 1) (by omega) ξ hξ
  refine ⟨t, ht, ?_⟩
  intro x y z L hL W hW
  obtain ⟨F, hF, hfirst, hzero⟩ := OneTargetPhysicalLift.exists_lift x y z L W hW
  let : FiniteDimensional F₂ ↥(W ⊓ squareClassSpace y L) := FiniteDimensional.of_injective F hF
  let labels : Coordinate s L → Module.Dual F₂ ↥(W ⊓ squareClassSpace y L) :=
    fun v ↦ (CoordinateForms.coordinateFamily (code (starts x y z) L) v).comp F
  obtain ⟨M, hM⟩ := DisjointRecoveryTheorem.disjoint_recovery_sharp
    (K := F₂) (U := ↥(W ⊓ squareClassSpace y L)) labels (s + 1) t (by omega) ht
  let P := M.map F
  have hno : NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t :=
    RecoveryImage.no_recovery_image F hF _ M (s + 1) t hM.2.1
  have hdim := RecoveryImage.finrank_image F hF M
  have hcard : Fintype.card (Coordinate s L) = (s + 2) * (L + 1) := by
    simp only [Coordinate, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  have hbudget : 2 * (Fintype.card (Coordinate s L) : ℝ) *
      DisjointRecoveryParameters.parameter (s + 1) t ≤ ξ * L / 4 := by
    rw [hcard]
    exact hcost L hL
  have hMcost := hM.1
  rw [Nat.cast_sub (Submodule.finrank_le M)] at hMcost
  refine ⟨P, hno, ?_, RecoveryImage.projection_image_injective F hF M _ _ rfl hfirst, ?_⟩
  · rw [hdim]
    linarith only [hMcost, hbudget]
  · ext u i
    obtain ⟨v, _hvM, hvu⟩ := Submodule.mem_map.mp u.property
    have h := congrFun (LinearMap.congr_fun hzero v) i
    change (projection (starts x y z) L (Sum.inr 1)) u.val i = 0
    rw [← hvu]
    exact h

end PaperP1.OneTargetPhysicalRegularization
