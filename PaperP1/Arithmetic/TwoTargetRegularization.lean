module

public import PaperP1.Arithmetic.TwoTargetWindowSections
public import PaperP1.Coding.SimultaneousProjectionRegularization
public import PaperP1.Coding.TargetLabelsComponents
public import PaperP1.Analysis.SmallRecoveryParameter

/-! # One physical regularization retains a dense projection in each actual target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections
  PaperP1.DisjointRecoveryTheorem PaperP1.RecoveryLabelSupports PaperP1.PhysicalLabelSupportCount

local instance twoTargetRegularizationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    Module F₂ S := S.module

local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

def coordinateForm {s y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → TwoTargetWindowSections.Even L))
    (σY : squareClassSpace y L →ₗ[F₂] TwoTargetWindowSections.Even L)
    (σZ : squareClassSpace z L →ₗ[F₂] TwoTargetWindowSections.Even L)
    (v : Coordinate s L) : Module.Dual F₂ (Kernel y z L W) :=
  (LinearMap.proj v).comp (physicalLift W σW σY σZ)

local instance dualDecidableEq {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (M : Submodule F₂ (Kernel y z L W)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem source_finite {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ⨆ i, squareClassSpace (x i) L) : FiniteDimensional F₂ W := by
  obtain ⟨σ, _hσ, hinj⟩ := EffectiveLinearSections.exists_section (sourceMap x L) W
    (by rwa [range_source_map])
  exact FiniteDimensional.of_injective σ hinj

theorem effective_dimension_formula {s : ℕ} (x : Fin s → ℕ) (y z L : ℕ)
    (W : Submodule F₂ (ℕ →₀ F₂)) (hW : W ≤ ⨆ i, squareClassSpace (x i) L) :
    Module.finrank F₂ (Kernel y z L W) =
      Module.finrank F₂ W + Module.finrank F₂ (squareClassSpace y L) +
        Module.finrank F₂ (squareClassSpace z L) -
        Module.finrank F₂ (W ⊔ (squareClassSpace y L ⊔ squareClassSpace z L) : Submodule F₂ (ℕ →₀ F₂)) := by
  let : FiniteDimensional F₂ W := source_finite x L W hW
  exact TwoTargetKernel.dimension_deficit W _ _

theorem uniform_regularization (s : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ x : Fin s → ℕ, ∀ y z L : ℕ, 1 ≤ L →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      Disjoint W (squareClassSpace y L) → Disjoint W (squareClassSpace z L) →
      ∃ σW : W →ₗ[F₂] (Fin s → TwoTargetWindowSections.Even L),
      ∃ σY : squareClassSpace y L →ₗ[F₂] TwoTargetWindowSections.Even L,
      ∃ σZ : squareClassSpace z L →ₗ[F₂] TwoTargetWindowSections.Even L,
        (sourceMap x L).comp σW = W.subtype ∧
        (evenSquareClassMap y L).comp σY = (squareClassSpace y L).subtype ∧
        (evenSquareClassMap z L).comp σZ = (squareClassSpace z L).subtype ∧
        (∀ j, Function.Injective (targetProjection W σY σZ j)) ∧
        ∃ M : Submodule F₂ (Kernel y z L W),
          RecoveryConclusion (coordinateForm W σW σY σZ) M (s + 1) t (t - 1) ∧
          ((Module.finrank F₂ (Kernel y z L W) - Module.finrank F₂ M : ℕ) : ℝ) ≤ ξ * L / 4 ∧
          (∀ j : Fin 2, (Module.finrank F₂ (Kernel y z L W) : ℝ) - ξ * L / 4 ≤
            (ProjectionLabelBudget.labels ((targetProjection W σY σZ j).comp M.subtype)).card) ∧
          (∀ j : Fin 2, ProjectionLabelBudget.labels ((targetProjection W σY σZ j).comp M.subtype) ⊆
            RecoveryLabelSupports.labels (K := F₂) (U := Kernel y z L W) (V := Coordinate s L)
              (coordinateForm W σW σY σZ) M) ∧
          ∀ α : Module.Dual F₂ M, α ≠ 0 →
            (supportPool (W := Module.Dual F₂ M) (V := Coordinate s L)
              (fun v ↦ (coordinateForm W σW σY σZ v).comp M.subtype)
              (RecoveryLabelSupports.labels (K := F₂) (U := Kernel y z L W) (V := Coordinate s L)
                (coordinateForm W σW σY σZ) M) (s + 1) α).card ≤
                supportBound (s + 1) t (t - 1) := by
  obtain ⟨t, ht, hcost⟩ := SmallRecoveryParameter.exists_relative_cost (s + 1) (by omega) ξ hξ
  refine ⟨t, ht, ?_⟩
  intro x y z L hL W hW hWY hWZ
  let : FiniteDimensional F₂ W := source_finite x L W hW
  obtain ⟨σW, σY, σZ, hσW, hσY, hσZ, _hWi, hYi, hZi⟩ := exists_sections x y z L W hW
  have hinj := target_projection_injective W σY σZ hYi hZi hWY hWZ
  let : FiniteDimensional F₂ (Kernel y z L W) :=
    FiniteDimensional.of_injective (targetProjection W σY σZ 0) (hinj 0)
  have hcoord : ∀ j r i, targetProjection W σY σZ j r i =
      coordinateForm W σW σY σZ (Sum.inr j, i) r := fun j r i ↦ target_coordinate W σW σY σZ j r i
  obtain ⟨M, hM, hlabels, hsub, hpools⟩ :=
    SimultaneousProjectionRegularization.common_regularization (coordinateForm W σW σY σZ)
      (targetProjection W σY σZ) (fun j i ↦ (Sum.inr j, i)) hcoord hinj (s + 1) t (by omega) ht
  have hcard : Fintype.card (Coordinate s L) = (s + 2) * (L + 1) := by
    simp only [Coordinate, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  have hbudget : 2 * (Fintype.card (Coordinate s L) : ℝ) *
      DisjointRecoveryParameters.parameter (s + 1) t ≤ ξ * L / 4 := by
    rw [hcard]
    exact hcost L hL
  exact ⟨σW, σY, σZ, hσW, hσY, hσZ, hinj, M, hM, hM.1.trans hbudget,
    fun j ↦ (by have h := hlabels j; linarith only [h, hbudget]), hsub, hpools⟩

theorem physical_class_budgets {s y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → TwoTargetWindowSections.Even L))
    (σY : squareClassSpace y L →ₗ[F₂] TwoTargetWindowSections.Even L)
    (σZ : squareClassSpace z L →ₗ[F₂] TwoTargetWindowSections.Even L)
    (hY : Function.Injective σY) (hZ : Function.Injective σZ)
    (hWY : Disjoint W (squareClassSpace y L)) (hWZ : Disjoint W (squareClassSpace z L))
    (M : Submodule F₂ (Kernel y z L W)) :
    let ℓ := fun v ↦ (coordinateForm W σW σY σZ v).comp M.subtype
    ∀ j : Fin 2,
      Module.finrank F₂ M ≤ (TargetComponentBudget.meeting (LabelClassPartition.parts ℓ)
        (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card ∧
      2 * Module.finrank F₂ M ≤ L + 1 +
        (TargetComponentBudget.singleton (LabelClassPartition.parts ℓ)
          (univ.image fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L))).card := by
  have hinj := target_projection_injective W σY σZ hY hZ hWY hWZ
  let : FiniteDimensional F₂ (Kernel y z L W) :=
    FiniteDimensional.of_injective (targetProjection W σY σZ 0) (hinj 0)
  intro ℓ j
  have hcoord : ∀ r : M, ∀ i : Fin (L + 1),
      ((targetProjection W σY σZ j).comp M.subtype) r i = ℓ (Sum.inr j, i) r :=
    fun r i ↦ target_coordinate W σW σY σZ j r.val i
  have htarget : Function.Injective (fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : Coordinate s L)) := by
    intro i k h
    exact (Prod.mk.inj h).2
  have h := TargetLabelsComponents.actual_class_budgets ℓ ((targetProjection W σY σZ j).comp M.subtype)
    (fun i ↦ ((Sum.inr j, i) : Coordinate s L)) hcoord ((hinj j).comp Subtype.val_injective) htarget
  simpa only [Fintype.card_fin] using h

theorem physical_class_size {s y z L d t : ℕ} (W : Submodule F₂ (ℕ →₀ F₂))
    (σW : W →ₗ[F₂] (Fin s → TwoTargetWindowSections.Even L))
    (σY : squareClassSpace y L →ₗ[F₂] TwoTargetWindowSections.Even L)
    (σZ : squareClassSpace z L →ₗ[F₂] TwoTargetWindowSections.Even L)
    (M : Submodule F₂ (Kernel y z L W))
    (hM : RecoveryConclusion (coordinateForm W σW σY σZ) M d t (t - 1)) :
    let ℓ := fun v ↦ (coordinateForm W σW σY σZ v).comp M.subtype
    ∀ D ∈ LabelClassPartition.parts ℓ, D.card ≤ t - 1 := by
  intro ℓ
  apply LabelClassPartition.part_size
  intro α hα
  exact hM.2.2.1 α hα

end PaperP1.TwoTargetRegularization
