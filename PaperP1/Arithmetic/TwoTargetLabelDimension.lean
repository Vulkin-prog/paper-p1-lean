module

public import PaperP1.Arithmetic.TwoTargetPhysicalBudgets
public import PaperP1.Arithmetic.TwoTargetLabelSelection

/-! # Each actual target label population separately bounds the regularized effective dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetLabelDimension

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations

local instance labelDimensionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((Fin s ⊕ Fin 2) × Fin (L + 1)) → F₂) (code X L)
local instance physicalAddCommGroup {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : AddCommGroup P := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ P) := Classical.decEq _

theorem dimension_le_labels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L))
    (hinj : ∀ j : Fin 2, Function.Injective ((projection X L (Sum.inr j)).comp P.subtype)) (j : Fin 2) :
    Module.finrank F₂ P ≤ (TwoTargetLabelSelection.targetLabels X P j).card := by
  have h := (TwoTargetPhysicalBudgets.class_budgets X P hinj j).1
  have heq := LabelClassPartition.meeting_card (TwoTargetPrimeClassSupports.label X P)
    (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L))
  exact h.trans_eq heq

end PaperP1.TwoTargetLabelDimension
