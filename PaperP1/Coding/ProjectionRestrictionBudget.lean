module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Basic.Real.Basic
public import Lean.Elab.Tactic.Omega

/-! # Restricting a relation space loses at most its codimension in every projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectionRestrictionBudget

variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U] [AddCommGroup W] [Module K W]

def kernelInclusion (f : U →ₗ[K] W) (M : Submodule K U) :
    LinearMap.ker (f.comp M.subtype) →ₗ[K] LinearMap.ker f where
  toFun x := ⟨x.val.val, x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K U] in
theorem kernelInclusion_injective (f : U →ₗ[K] W) (M : Submodule K U) :
    Function.Injective (kernelInclusion f M) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker f ↦ z.val) hxy

theorem rank_loss_le_codimension (f : U →ₗ[K] W) (M : Submodule K U) :
    Module.finrank K (LinearMap.range f) ≤ Module.finrank K (LinearMap.range (f.comp M.subtype)) +
      (Module.finrank K U - Module.finrank K M) := by
  have hker := LinearMap.finrank_le_finrank_of_injective (kernelInclusion_injective f M)
  have hfull := f.finrank_range_add_finrank_ker
  have hpart := (f.comp M.subtype).finrank_range_add_finrank_ker
  have hdim := Submodule.finrank_le M
  omega

theorem real_rank_lower_bound (f : U →ₗ[K] W) (M : Submodule K U) :
    (Module.finrank K (LinearMap.range f) : ℝ) -
      ((Module.finrank K U - Module.finrank K M : ℕ) : ℝ) ≤
        Module.finrank K (LinearMap.range (f.comp M.subtype)) := by
  have h : (Module.finrank K (LinearMap.range f) : ℝ) ≤
      Module.finrank K (LinearMap.range (f.comp M.subtype)) +
        ((Module.finrank K U - Module.finrank K M : ℕ) : ℝ) := by
    exact_mod_cast rank_loss_le_codimension f M
  linarith only [h]

end PaperP1.ProjectionRestrictionBudget
