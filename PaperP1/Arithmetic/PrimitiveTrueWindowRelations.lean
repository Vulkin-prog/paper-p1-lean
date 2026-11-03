module

public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Affine.PrimitiveCoordinateProjection
public import PaperP1.Affine.RetainedNullity
public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Model.CompatibleNullityBound

/-! # Primitive true-window families have injective effective projections

Every pair in a primitive family of size at least three is disjoint.
No local full-rank or affine compatibility assumption is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveTrueWindowRelations

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ConnectedWindowFamilies PaperP1.Model.InfiniteStarts

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance effectiveAddCommGroup (I : Finset ℕ) (L : ℕ) :
    AddCommGroup (EffectiveKernel (fun i : I ↦ i.val) L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := (i : I) → squareClassSpace i.val L)
      (EffectiveKernel (fun i : I ↦ i.val) L)

theorem dimension (I : Finset ℕ) (L : ℕ) :
    Module.finrank F₂ (EffectiveKernel (fun i : I ↦ i.val) L) = runRelativeNullity L I := rfl

theorem projection_injective (I : Finset ℕ) (L : ℕ) (hprim : Primitive L I) (i : I) :
    Function.Injective (effectiveProjection (fun j : I ↦ j.val) L i) :=
  PrimitiveCoordinateProjection.injective (fun x ↦ squareClassSpace x L) I hprim.2 i

theorem pair_disjoint (I : Finset ℕ) (L : ℕ) (hcard : 3 ≤ I.card) (hprim : Primitive L I)
    (i j : I) (hij : i ≠ j) : Disjoint (squareClassSpace i.val L) (squareClassSpace j.val L) := by
  have hne : i.val ≠ j.val := fun he ↦ hij (Subtype.ext he)
  have hsub : ({i.val, j.val} : Finset ℕ) ⊆ I := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact i.property
    · exact mem_singleton.mp hx ▸ j.property
  have hproper : ({i.val, j.val} : Finset ℕ) ⊂ I := by
    apply ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro he
    have hc := card_pair hne
    rw [he] at hc
    omega
  have hz := hprim.2 {i.val, j.val} hproper
  rw [RetainedNullity.nullity_pair_eq_intersection (fun x ↦ squareClassSpace x L) i.val j.val hne] at hz
  exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hz)

end PaperP1.PrimitiveTrueWindowRelations
