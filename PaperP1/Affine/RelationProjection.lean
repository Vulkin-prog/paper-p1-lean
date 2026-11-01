module

public import PaperP1.Affine.RelativeNullity
public import Mathlib.Data.Fintype.BigOperators

/-! # The increment of effective nullity is the dimension of the new-block projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationProjection

open Finset PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι]
variable (S : Option ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

abbrev Kernel := LinearMap.ker (relationAddition S)

def projection (i : Option ι) : Kernel S →ₗ[𝔽₂] S i :=
  (LinearMap.proj i).comp (Kernel S).subtype

def kernelEquiv : LinearMap.ker (relationAddition (fun i : ι ↦ S (some i))) ≃ₗ[𝔽₂]
    LinearMap.ker (projection S none) where
  toFun r := by
    let s : (i : Option ι) → S i := fun i ↦ match i with
      | none => 0
      | some j => r.val j
    have hs : relationAddition S s = 0 := by
      change (∑ i : Option ι, (s i).val) = 0
      rw [Fintype.sum_option]
      change (0 : U) + (∑ j : ι, (r.val j).val) = 0
      have hr := r.property
      change (∑ j : ι, (r.val j).val) = 0 at hr
      simpa only [zero_add] using hr
    exact ⟨⟨s, hs⟩, rfl⟩
  invFun r := by
    refine ⟨(fun j ↦ r.val.val (some j)), ?_⟩
    have hfull := r.val.property
    have hnone : r.val.val none = 0 := r.property
    change (∑ i : Option ι, (r.val.val i).val) = 0 at hfull
    rw [Fintype.sum_option, hnone, Submodule.coe_zero, zero_add] at hfull
    exact hfull
  left_inv r := by
    apply Subtype.ext
    funext i
    rfl
  right_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i with
    | none => exact r.property.symm
    | some _ => rfl
  map_add' r s := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i with
    | none => exact (add_zero (0 : S none)).symm
    | some _ => rfl
  map_smul' c r := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    cases i <;> simp

theorem projection_dimension_identity :
    Module.finrank 𝔽₂ (LinearMap.range (projection S none)) +
      relativeNullity (fun i : ι ↦ S (some i)) = relativeNullity S := by
  have h := (projection S none).finrank_range_add_finrank_ker
  rw [← (kernelEquiv S).finrank_eq] at h
  exact h

theorem nullity_increment :
    relativeNullity S - relativeNullity (fun i : ι ↦ S (some i)) =
      Module.finrank 𝔽₂ (LinearMap.range (projection S none)) := by
  have h := projection_dimension_identity S
  omega

end PaperP1.RelationProjection
