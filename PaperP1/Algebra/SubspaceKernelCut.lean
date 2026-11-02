module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The dimension retained by an image-rank cut followed by finitely many coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubspaceKernelCut

theorem finrank_lower {K E M F : Type*} [DivisionRing K]
    [AddCommGroup E] [Module K E] [Module.Finite K E]
    [AddCommGroup M] [Module K M] [AddCommGroup F] [Module K F] [Module.Finite K F]
    (f : E →ₗ[K] M) (g : E →ₗ[K] F) (r : ℕ)
    (hf : Module.finrank K (LinearMap.range f) ≤ r) :
    Module.finrank K E - r - Module.finrank K F ≤
      Module.finrank K (LinearMap.ker (g.comp (LinearMap.ker f).subtype)) := by
  have hfirst := f.finrank_range_add_finrank_ker
  have hsecond := (g.comp (LinearMap.ker f).subtype).finrank_range_add_finrank_ker
  have hsmall := (LinearMap.range (g.comp (LinearMap.ker f).subtype)).finrank_le
  omega

end PaperP1.SubspaceKernelCut
