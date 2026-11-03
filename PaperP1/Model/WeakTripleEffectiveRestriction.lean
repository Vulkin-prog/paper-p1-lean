module

public import PaperP1.Arithmetic.PrimitiveTrueWindowRelations
public import PaperP1.Affine.RelationProjectionRank
public import PaperP1.Coding.CommonInjectiveRestriction

/-! # Small proper intersections give a large common injective effective triple subspace -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakTripleEffectiveRestriction

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations PaperP1.Model.InfiniteStarts

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup (I : Finset ℕ) (L : ℕ) : AddCommGroup (code (fun i : I ↦ i.val) L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := ((I × Fin (L + 1)) → F₂)) (code (fun i : I ↦ i.val) L)
local instance effectiveAddCommGroup (I : Finset ℕ) (L : ℕ) :
    AddCommGroup (EffectiveKernel (fun i : I ↦ i.val) L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := (i : I) → squareClassSpace i.val L)
      (EffectiveKernel (fun i : I ↦ i.val) L)
local instance effectiveSubspaceAddCommGroup (I : Finset ℕ) (L : ℕ)
    (R : Submodule F₂ (EffectiveKernel (fun i : I ↦ i.val) L)) : AddCommGroup R := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := EffectiveKernel (fun i : I ↦ i.val) L) R

theorem kernel_finrank (I : Finset ℕ) (L : ℕ) (i : I) :
    Module.finrank F₂ (LinearMap.ker (effectiveProjection (fun j : I ↦ j.val) L i)) =
      runRelativeNullity L (I.erase i.val) :=
  RelationProjectionRank.kernel_finrank (fun x ↦ squareClassSpace x L) I i

theorem kernel_bound (I : Finset ℕ) (L : ℕ) (hcard : I.card = 3) (W : ℝ)
    (hweak : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ W) (i : I) :
    (Module.finrank F₂ (LinearMap.ker (effectiveProjection (fun j : I ↦ j.val) L i)) : ℝ) ≤ W := by
  have hc : (I.erase i.val).card = 2 := by rw [card_erase_of_mem i.property, hcard]
  obtain ⟨x, y, hxy, he⟩ := card_eq_two.mp hc
  have hx : x ∈ I := mem_of_mem_erase (by rw [he]; exact mem_insert_self x {y})
  have hy : y ∈ I := mem_of_mem_erase (by rw [he]; exact mem_insert_of_mem (mem_singleton_self y))
  rw [kernel_finrank, he, runRelativeNullity,
    RetainedNullity.nullity_pair_eq_intersection (fun x ↦ squareClassSpace x L) x y hxy]
  exact hweak x hx y hy hxy

theorem exists_restriction (I : Finset ℕ) (L : ℕ) (hcard : I.card = 3) (W : ℝ)
    (hweak : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ W) :
    ∃ R : Submodule F₂ (EffectiveKernel (fun i : I ↦ i.val) L),
      (runRelativeNullity L I : ℝ) - 3 * W ≤ Module.finrank F₂ R ∧
      ∀ i, Function.Injective ((effectiveProjection (fun j : I ↦ j.val) L i).comp R.subtype) := by
  let : FiniteDimensional F₂ (EffectiveKernel (fun i : I ↦ i.val) L) :=
    FiniteDimensional.of_surjective (toEffective (fun i : I ↦ i.val) L)
      (toEffective_surjective (fun i : I ↦ i.val) L)
  obtain ⟨R, hcost, hinj⟩ := CommonInjectiveRestriction.exists_subspace
    (K := F₂) (U := EffectiveKernel (fun i : I ↦ i.val) L)
    (V := fun i : I ↦ squareClassSpace i.val L)
    (fun i : I ↦ effectiveProjection (fun j : I ↦ j.val) L i)
  have hsum : (∑ i : I, (Module.finrank F₂ (LinearMap.ker
      (effectiveProjection (fun j : I ↦ j.val) L i)) : ℝ)) ≤ 3 * W := by
    calc
      _ ≤ ∑ _i : I, W := sum_le_sum fun i _hi ↦ kernel_bound I L hcard W hweak i
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, hcard]; norm_num
  have hcostR : (Module.finrank F₂ (EffectiveKernel (fun i : I ↦ i.val) L) : ℝ) ≤
      (Module.finrank F₂ R : ℝ) + ∑ i : I, (Module.finrank F₂ (LinearMap.ker
        (effectiveProjection (fun j : I ↦ j.val) L i)) : ℝ) := by exact_mod_cast hcost
  rw [PrimitiveTrueWindowRelations.dimension] at hcostR
  exact ⟨R, by linarith only [hcostR, hsum], hinj⟩

end PaperP1.WeakTripleEffectiveRestriction
