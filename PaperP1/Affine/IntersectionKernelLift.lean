module

public import PaperP1.Affine.TwoTargetKernel

/-! # An actual source-target intersection embeds in a two-target relation kernel with zero auxiliary target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntersectionKernelLift

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]

def embed (W Y Z : Submodule K U) : ↥(W ⊓ Y) →ₗ[K] TwoTargetKernel.Kernel W Y Z :=
  ((Submodule.inclusion (show W ⊓ Y ≤ W from inf_le_left)).prod
    ((-(Submodule.inclusion (show W ⊓ Y ≤ Y from inf_le_right))).prod (0 : ↥(W ⊓ Y) →ₗ[K] Z))).codRestrict _
      (fun u ↦ by change (u.val : U) + -u.val + 0 = 0; simp)

theorem left_projection (W Y Z : Submodule K U) :
    (TwoTargetKernel.leftProjection W Y Z).comp (embed W Y Z) =
      -(Submodule.inclusion (show W ⊓ Y ≤ Y from inf_le_right)) := rfl

theorem right_projection (W Y Z : Submodule K U) :
    (TwoTargetKernel.rightProjection W Y Z).comp (embed W Y Z) = 0 := rfl

theorem left_projection_injective (W Y Z : Submodule K U) :
    Function.Injective ((TwoTargetKernel.leftProjection W Y Z).comp (embed W Y Z)) := by
  intro u v huv
  apply Subtype.ext
  have h : -u.val = -v.val := congrArg Subtype.val huv
  exact neg_injective h

end PaperP1.IntersectionKernelLift
