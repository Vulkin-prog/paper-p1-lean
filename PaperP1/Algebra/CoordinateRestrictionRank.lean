module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Finset.Card

/-! # The exact cost of setting any chosen coordinates to zero -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateRestrictionRank

open Finset

variable {K V : Type*} [DivisionRing K] [Fintype V]

def zeroed (R : Submodule K (V → K)) (D : Finset V) : Submodule K (V → K) where
  carrier := {f | f ∈ R ∧ ∀ v ∈ D, f v = 0}
  zero_mem' := ⟨R.zero_mem, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨R.add_mem hf.1 hg.1, fun v hv ↦ by simp only [Pi.add_apply, hf.2 v hv, hg.2 v hv, add_zero]⟩
  smul_mem' := by
    intro a f hf
    exact ⟨R.smul_mem a hf.1, fun v hv ↦ by simp only [Pi.smul_apply, hf.2 v hv, smul_zero]⟩

def restriction (R : Submodule K (V → K)) (D : Finset V) : R →ₗ[K] (D → K) where
  toFun f v := f.val v.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def kernelEquiv (R : Submodule K (V → K)) (D : Finset V) :
    LinearMap.ker (restriction R D) ≃ₗ[K] zeroed R D where
  toFun f := ⟨f.val.val, f.val.property, fun v hv ↦ congrFun f.property ⟨v, hv⟩⟩
  invFun f := ⟨⟨f.val, f.property.1⟩, funext (fun v ↦ f.property.2 v.val v.property)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

omit [Fintype V] in
theorem zeroed_le (R : Submodule K (V → K)) (D : Finset V) : zeroed R D ≤ R := fun _ hf ↦ hf.1

theorem zeroed_rank_le (R : Submodule K (V → K)) (D : Finset V) :
    Module.finrank K (zeroed R D) ≤ Module.finrank K R := Submodule.finrank_mono (zeroed_le R D)

theorem cover_cost (R : Submodule K (V → K)) (D : Finset V) :
    Module.finrank K R ≤ D.card + Module.finrank K (zeroed R D) := by
  have h := (restriction R D).finrank_range_add_finrank_ker
  have hdim := Submodule.finrank_le (LinearMap.range (restriction R D))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hdim
  rw [(kernelEquiv R D).finrank_eq] at h
  omega

end PaperP1.CoordinateRestrictionRank
