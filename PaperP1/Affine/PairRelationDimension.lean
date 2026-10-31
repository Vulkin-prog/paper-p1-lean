module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

/-! # Local kernels and the common image of a complete pair relation -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.Affine

theorem finrank_coprod_kernel_eq
    {K A B U : Type*} [DivisionRing K]
    [AddCommGroup A] [Module K A] [Module.Finite K A]
    [AddCommGroup B] [Module K B] [Module.Finite K B]
    [AddCommGroup U] [Module K U] (f : A →ₗ[K] U) (g : B →ₗ[K] U) :
    Module.finrank K (LinearMap.ker (f.coprod g)) =
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g) +
        Module.finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K U) := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hpair := (f.coprod g).finrank_range_add_finrank_ker
  rw [LinearMap.range_coprod, Module.finrank_prod] at hpair
  have hint := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
  omega

end PaperP1.Affine
