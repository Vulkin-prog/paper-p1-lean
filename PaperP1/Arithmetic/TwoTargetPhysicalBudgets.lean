module

public import PaperP1.Arithmetic.TwoTargetPhysicalRegularization

/-! # Separate literal target-class budgets on the image of the effective relation kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPhysicalBudgets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.DisjointRecoverySubspace

local instance physicalBudgetsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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

theorem class_budgets {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L))
    (hinj : ∀ j : Fin 2, Function.Injective ((projection X L (Sum.inr j)).comp P.subtype)) :
    let ℓ := fun v ↦ (CoordinateForms.coordinateFamily (code X L) v).comp P.subtype
    ∀ j : Fin 2,
      Module.finrank F₂ P ≤ (TargetComponentBudget.meeting (LabelClassPartition.parts ℓ)
        (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card ∧
      2 * Module.finrank F₂ P ≤ L + 1 +
        (TargetComponentBudget.singleton (LabelClassPartition.parts ℓ)
          (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card := by
  intro ℓ j
  have hcoord : ∀ r : P, ∀ i : Fin (L + 1),
      ((projection X L (Sum.inr j)).comp P.subtype) r i = ℓ (Sum.inr j, i) r := fun _ _ ↦ rfl
  have htarget : Function.Injective (fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L)) := by
    intro i k h
    exact (Prod.mk.inj h).2
  simpa only [Fintype.card_fin] using TargetLabelsComponents.actual_class_budgets ℓ
    ((projection X L (Sum.inr j)).comp P.subtype) (fun i ↦ ((Sum.inr j, i) : Coordinate s L))
    hcoord (hinj j) htarget

theorem class_size {s L t : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L))
    (hno : NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) P (s + 1) t) :
    let ℓ := fun v ↦ (CoordinateForms.coordinateFamily (code X L) v).comp P.subtype
    ∀ D ∈ LabelClassPartition.parts ℓ, D.card ≤ t - 1 := by
  intro ℓ
  apply LabelClassPartition.part_size
  exact coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code X L)) P
    (s + 1) t (by omega) hno

theorem uniform_class_data (s : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ x : Fin s → ℕ, ∀ y z L : ℕ, 1 ≤ L →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      Disjoint W (squareClassSpace y L) → Disjoint W (squareClassSpace z L) →
      ∃ P : Submodule F₂ (code (starts x y z) L),
        NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t ∧
        (Module.finrank F₂ (Kernel y z L W) : ℝ) - ξ * L / 4 ≤ Module.finrank F₂ P ∧
        (let ℓ := fun v ↦ (CoordinateForms.coordinateFamily (code (starts x y z) L) v).comp P.subtype
         (∀ D ∈ LabelClassPartition.parts ℓ, D.card ≤ t - 1) ∧
         ∀ j : Fin 2,
           Module.finrank F₂ P ≤ (TargetComponentBudget.meeting (LabelClassPartition.parts ℓ)
             (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card ∧
           2 * Module.finrank F₂ P ≤ L + 1 +
             (TargetComponentBudget.singleton (LabelClassPartition.parts ℓ)
               (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card) := by
  obtain ⟨t, ht, hu⟩ := TwoTargetPhysicalRegularization.uniform_physical_subspace s ξ hξ
  refine ⟨t, ht, ?_⟩
  intro x y z L hL W hW hWY hWZ
  obtain ⟨P, hno, hdim, hinj⟩ := hu x y z L hL W hW hWY hWZ
  exact ⟨P, hno, hdim, class_size _ P hno, class_budgets _ P hinj⟩

end PaperP1.TwoTargetPhysicalBudgets
