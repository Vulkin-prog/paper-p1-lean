module

public import PaperP1.Affine.IntersectionKernelLift
public import PaperP1.Arithmetic.TwoTargetCodeLift

/-! # The actual effective source-target intersection has a physical lift with injective first target and zero auxiliary target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneTargetPhysicalLift

open PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections PaperP1.PhysicalWindowRelations

local instance oneTargetLiftPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem exists_lift {s : ℕ} (x : Fin s → ℕ) (y z L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ⨆ i, squareClassSpace (x i) L) :
    ∃ F : ↥(W ⊓ squareClassSpace y L) →ₗ[F₂] code (starts x y z) L,
      Function.Injective F ∧ Function.Injective ((projection (starts x y z) L (Sum.inr 0)).comp F) ∧
        (projection (starts x y z) L (Sum.inr 1)).comp F = 0 := by
  obtain ⟨σW, σY, σZ, hσW, hσY, hσZ, _hWi, hYi, _hZi⟩ := exists_sections x y z L W hW
  let E := IntersectionKernelLift.embed W (squareClassSpace y L) (squareClassSpace z L)
  let F := (TwoTargetCodeLift.toCode x W σW σY σZ hσW hσY hσZ).comp E
  have hinj : Function.Injective ((projection (starts x y z) L (Sum.inr 0)).comp F) := by
    intro u v huv
    apply IntersectionKernelLift.left_projection_injective W (squareClassSpace y L) (squareClassSpace z L)
    apply hYi
    apply Subtype.ext
    exact huv
  refine ⟨F, ?_, hinj, ?_⟩
  · intro u v huv
    exact hinj (congrArg (projection (starts x y z) L (Sum.inr 0)) huv)
  · ext u i
    change (σZ 0).val i = 0
    rw [map_zero]
    rfl

end PaperP1.OneTargetPhysicalLift
