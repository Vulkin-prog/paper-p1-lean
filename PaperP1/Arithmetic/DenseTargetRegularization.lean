module

public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Affine.RelationProjection
public import PaperP1.Coding.RegularizedProjection
public import PaperP1.Analysis.SmallRecoveryParameter

/-! # The actual new-window nullity increment retains a large regularized label set

Sources may overlap or be dependent. The finite code keeps all physical
vertex copies, while the loss is computed on the effective square-class
images. The recovery order is fixed before the length and every start.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTargetRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.DisjointRecoveryTheorem PaperP1.PhysicalLabelSupportCount

local instance denseTargetRegularizationTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

local instance denseTargetDecEq (W : Type*) : DecidableEq W := Classical.decEq _

abbrev targetLabels {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) :=
  ProjectionLabelBudget.labels (K := F₂) (U := M) (I := Fin (L + 1))
    ((projection X L none).comp M.subtype)

def loss {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) : ℕ :=
  relativeNullity (fun i ↦ squareClassSpace (X i) L) -
    relativeNullity (fun i : Fin s ↦ squareClassSpace (X (some i)) L)

theorem loss_eq_effective_projection_rank {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) :
    loss X L = Module.finrank F₂ (LinearMap.range (effectiveProjection X L none)) :=
  RelationProjection.nullity_increment (fun i ↦ squareClassSpace (X i) L)

theorem loss_le_physical_projection_rank {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) :
    loss X L ≤ Module.finrank F₂ (LinearMap.range (projection X L none)) := by
  rw [loss_eq_effective_projection_rank]
  exact effective_projection_rank_le X L none

theorem uniform_regularization (s : ℕ) (hs : 1 ≤ s) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ X : Option (Fin s) → ℕ, ∀ L : ℕ, 1 ≤ L →
      ∃ M : Submodule F₂ (code X L),
        RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1) ∧
        (loss X L : ℝ) - η * L / 4 ≤
          (targetLabels X L M).card ∧
        targetLabels X L M ⊆
          RecoveryLabelSupports.labels (CoordinateForms.coordinateFamily (code X L)) M ∧
        ∀ α : Module.Dual F₂ M, α ≠ 0 →
          (supportPool
            (fun v ↦ (CoordinateForms.coordinateFamily (code X L) v).comp M.subtype)
            (RecoveryLabelSupports.labels (CoordinateForms.coordinateFamily (code X L)) M) s α).card ≤
              supportBound s t (t - 1) := by
  obtain ⟨t, ht, hsmall⟩ := SmallRecoveryParameter.exists_relative_cost s hs η hη
  refine ⟨t, ht, ?_⟩
  intro X L hL
  let R := code X L
  let labels := CoordinateForms.coordinateFamily R
  let f := projection X L none
  let target : Fin (L + 1) → Option (Fin s) × Fin (L + 1) := fun i ↦ (none, i)
  have hcoord : ∀ u i, f u i = labels (target i) u := fun _ _ ↦ rfl
  obtain ⟨M, hM, hlabels, hsub, hpools⟩ :=
    RegularizedProjection.regularized_projection labels f target hcoord s t hs ht
  refine ⟨M, hM, ?_, hsub, hpools⟩
  have hcard : Fintype.card (Option (Fin s) × Fin (L + 1)) = (s + 1) * (L + 1) := by
    simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  have hcost := hsmall L hL
  have hloss : (loss X L : ℝ) ≤ Module.finrank F₂ (LinearMap.range f) := by
    exact_mod_cast loss_le_physical_projection_rank X L
  rw [hcard] at hlabels
  linarith only [hlabels, hcost, hloss]

end PaperP1.DenseTargetRegularization
