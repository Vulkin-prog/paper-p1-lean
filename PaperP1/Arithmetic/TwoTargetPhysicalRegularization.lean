module

public import PaperP1.Arithmetic.TwoTargetCodeLift
public import PaperP1.Arithmetic.TwoTargetIntrinsicClassCoefficients

/-! # The regularized effective relation kernel gives an intrinsic physical-code subspace of the correct dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPhysicalRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections
  PaperP1.DisjointRecoverySubspace PaperP1.PhysicalWindowRelations

local instance physicalRegularizationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem uniform_physical_subspace (s : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ x : Fin s → ℕ, ∀ y z L : ℕ, 1 ≤ L →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (x i) L →
      Disjoint W (squareClassSpace y L) → Disjoint W (squareClassSpace z L) →
      ∃ P : Submodule F₂ (code (starts x y z) L),
        NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t ∧
        (Module.finrank F₂ (Kernel y z L W) : ℝ) - ξ * L / 4 ≤ Module.finrank F₂ P ∧
        ∀ j : Fin 2, Function.Injective ((projection (starts x y z) L (Sum.inr j)).comp P.subtype) := by
  obtain ⟨t, ht, hu⟩ := TwoTargetRegularization.uniform_regularization s ξ hξ
  refine ⟨t, ht, ?_⟩
  intro x y z L hL W hW hWY hWZ
  obtain ⟨σW, σY, σZ, hσW, hσY, hσZ, hinj, M, hM, hcost, _hlabels, _hsub, _hpools⟩ :=
    hu x y z L hL W hW hWY hWZ
  let F := TwoTargetCodeLift.toCode x W σW σY σZ hσW hσY hσZ
  have hF : Function.Injective F := TwoTargetCodeLift.injective_of_target x W σW σY σZ hσW hσY hσZ 0 (hinj 0)
  let : FiniteDimensional F₂ (Kernel y z L W) := FiniteDimensional.of_injective F hF
  let P := M.map F
  have hforms : (fun v ↦ (CoordinateForms.coordinateFamily (code (starts x y z) L) v).comp F) =
      TwoTargetRegularization.coordinateForm W σW σY σZ := by
    funext v
    exact TwoTargetCodeLift.coordinate_pullback x W σW σY σZ hσW hσY hσZ v
  have hno : NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t := by
    apply RecoveryImage.no_recovery_image F hF
    rw [hforms]
    exact hM.2.1
  have hdim : Module.finrank F₂ P = Module.finrank F₂ M := RecoveryImage.finrank_image F hF M
  have hMle := Submodule.finrank_le M
  rw [Nat.cast_sub hMle] at hcost
  refine ⟨P, hno, ?_, ?_⟩
  · rw [hdim]
    linarith only [hcost]
  · intro j
    exact RecoveryImage.projection_image_injective F hF M (targetProjection W σY σZ j)
      (projection (starts x y z) L (Sum.inr j))
      (TwoTargetCodeLift.target_projection x W σW σY σZ hσW hσY hσZ j) (hinj j)

end PaperP1.TwoTargetPhysicalRegularization
