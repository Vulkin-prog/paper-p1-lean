module

public import PaperP1.Arithmetic.TwoTargetWindowSections
public import PaperP1.Model.FreeComponentRank

/-! # With no source, the effective two-target kernel has the actual intersection dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetEmptySource

open PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂)
      (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem dimension (y z L : ℕ) :
    Module.finrank F₂ (Kernel y z L ⊥) = FreeComponentRank.pairIntersectionRank y z L := by
  have hk := TwoTargetKernel.dimension_identity (⊥ : Submodule F₂ (ℕ →₀ F₂))
    (squareClassSpace y L) (squareClassSpace z L)
  have hs : (⊥ : Submodule F₂ (ℕ →₀ F₂)) ⊔ (squareClassSpace y L ⊔ squareClassSpace z L) =
      squareClassSpace y L ⊔ squareClassSpace z L := bot_sup_eq _
  rw [hs, finrank_bot, zero_add] at hk
  change Module.finrank F₂ (squareClassSpace y L) + Module.finrank F₂ (squareClassSpace z L) =
    Module.finrank F₂ (squareClassSpace y L ⊔ squareClassSpace z L : Submodule F₂ (ℕ →₀ F₂)) +
      Module.finrank F₂ (Kernel y z L ⊥) at hk
  have hi := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace y L) (squareClassSpace z L)
  unfold FreeComponentRank.pairIntersectionRank
  omega

end PaperP1.TwoTargetEmptySource
