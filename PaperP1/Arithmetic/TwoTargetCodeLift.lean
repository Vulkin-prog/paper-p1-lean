module

public import PaperP1.Arithmetic.TwoTargetRegularization
public import PaperP1.Coding.RecoveryImage

/-! # The exact effective two-target relation space embeds in the literal physical prime-equation code -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetCodeLift

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections

local instance twoTargetCodeLiftTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {s y z L : ℕ} (x : Fin s → ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
  (σW : W →ₗ[F₂] (Fin s → TwoTargetWindowSections.Even L))
  (σY : squareClassSpace y L →ₗ[F₂] TwoTargetWindowSections.Even L)
  (σZ : squareClassSpace z L →ₗ[F₂] TwoTargetWindowSections.Even L)
  (hW : (sourceMap x L).comp σW = W.subtype)
  (hY : (evenSquareClassMap y L).comp σY = (squareClassSpace y L).subtype)
  (hZ : (evenSquareClassMap z L).comp σZ = (squareClassSpace z L).subtype)

def toCode : Kernel y z L W →ₗ[F₂] PhysicalWindowRelations.code (starts x y z) L :=
  (physicalLift W σW σY σZ).codRestrict _ (fun r ↦
    ⟨physical_even W σW σY σZ r, physical_relation x W σW σY σZ hW hY hZ r⟩)

theorem target_projection (j : Fin 2) :
    (PhysicalWindowRelations.projection (starts x y z) L (Sum.inr j)).comp
      (toCode x W σW σY σZ hW hY hZ) = targetProjection W σY σZ j := by
  ext r i
  exact (target_coordinate W σW σY σZ j r i).symm

theorem coordinate_pullback (v : Coordinate s L) :
    (CoordinateForms.coordinateFamily (PhysicalWindowRelations.code (starts x y z) L) v).comp
      (toCode x W σW σY σZ hW hY hZ) = TwoTargetRegularization.coordinateForm W σW σY σZ v := by
  ext r
  rfl

theorem injective_of_target (j : Fin 2) (hinj : Function.Injective (targetProjection W σY σZ j)) :
    Function.Injective (toCode x W σW σY σZ hW hY hZ) := by
  intro r q hrq
  apply hinj
  have h := congrArg (PhysicalWindowRelations.projection (starts x y z) L (Sum.inr j)) hrq
  change ((PhysicalWindowRelations.projection (starts x y z) L (Sum.inr j)).comp
    (toCode x W σW σY σZ hW hY hZ)) r =
    ((PhysicalWindowRelations.projection (starts x y z) L (Sum.inr j)).comp
      (toCode x W σW σY σZ hW hY hZ)) q at h
  rw [target_projection] at h
  exact h

theorem to_code_injective (hYi : Function.Injective σY) (hZi : Function.Injective σZ)
    (hWY : Disjoint W (squareClassSpace y L)) (hWZ : Disjoint W (squareClassSpace z L)) :
    Function.Injective (toCode x W σW σY σZ hW hY hZ) :=
  injective_of_target x W σW σY σZ hW hY hZ 0 (target_projection_injective W σY σZ hYi hZi hWY hWZ 0)

end PaperP1.TwoTargetCodeLift
