module

public import PaperP1.Arithmetic.ActivePhysicalPrimeGroups
public import PaperP1.Arithmetic.OffsetNonalignmentFrom
public import PaperP1.Coding.RecoveryImage

/-! # Exact index transport of actual physical relation subspaces

Coordinate activity, each selected projection and the distinguished-block
nonalignment condition are transported without changing the dimension.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalWindowReindex

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ActivePhysicalPrimeGroups

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {J : Type*} [Fintype J] (X : J → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((J × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup {J : Type*} [Fintype J] (X : J → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

def reindex (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι) : code X L ≃ₗ[F₂] code (fun j ↦ X (e j)) L where
  toFun w := ⟨fun v ↦ w.val (e v.1, v.2), by
    constructor
    · intro j
      exact w.property.1 (e j)
    · exact (Fintype.sum_equiv e _ _ (fun _ ↦ rfl)).trans w.property.2⟩
  invFun w := ⟨fun v ↦ w.val (e.symm v.1, v.2), by
    constructor
    · intro i
      exact w.property.1 (e.symm i)
    · apply (Fintype.sum_equiv e.symm _ _ ?_).trans w.property.2
      intro i
      simp only [Equiv.apply_symm_apply]⟩
  left_inv w := by
    apply Subtype.ext
    funext v
    rcases v with ⟨i, u⟩
    simp only [Equiv.apply_symm_apply]
  right_inv w := by
    apply Subtype.ext
    funext v
    rcases v with ⟨j, u⟩
    simp only [Equiv.symm_apply_apply]
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem reindex_apply (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι) (w : code X L)
    (j : κ) (u : Fin (L + 1)) : (reindex X L e w).val (j, u) = w.val (e j, u) := rfl

theorem projection_comp (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι) (j : κ) :
    (projection (fun k ↦ X (e k)) L j).comp (reindex X L e).toLinearMap = projection X L (e j) := by
  ext w u
  rfl

theorem finrank_image (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι) (M : Submodule F₂ (code X L)) :
    Module.finrank F₂ (M.map (reindex X L e).toLinearMap) = Module.finrank F₂ M :=
  RecoveryImage.finrank_image _ (reindex X L e).injective M

theorem projection_image_injective (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι)
    (M : Submodule F₂ (code X L)) (j : κ)
    (hinj : Function.Injective ((projection X L (e j)).comp M.subtype)) :
    Function.Injective ((projection (fun k ↦ X (e k)) L j).comp
      (M.map (reindex X L e).toLinearMap).subtype) := by
  let E := Submodule.equivMapOfInjective (reindex X L e).toLinearMap (reindex X L e).injective M
  intro a b hab
  obtain ⟨u, rfl⟩ := E.surjective a
  obtain ⟨v, rfl⟩ := E.surjective b
  apply congrArg E
  apply hinj
  exact hab

theorem label_pullback (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι) (M : Submodule F₂ (code X L))
    (v : κ × Fin (L + 1)) :
    (label (fun j ↦ X (e j)) L (M.map (reindex X L e).toLinearMap) v).comp
      (Submodule.equivMapOfInjective (reindex X L e).toLinearMap (reindex X L e).injective M).toLinearMap =
      label X L M (e v.1, v.2) := by
  ext w
  rfl

theorem active_pullback (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι) (M : Submodule F₂ (code X L))
    (v : κ × Fin (L + 1))
    (hv : label (fun j ↦ X (e j)) L (M.map (reindex X L e).toLinearMap) v ≠ 0) :
    label X L M (e v.1, v.2) ≠ 0 := by
  have hh := RecoveryImage.pullback_ne_zero
    (Submodule.equivMapOfInjective (reindex X L e).toLinearMap (reindex X L e).injective M) _ hv
  rwa [label_pullback] at hh

theorem noExactFrom_reindex (X : ι → ℕ) (L : ℕ) (e : κ ≃ ι)
    (M : Submodule F₂ (code X L)) (j : κ)
    (h : OffsetNonalignmentFrom.NoExactFrom X L (fun v ↦ label X L M v ≠ 0) (e j)) :
    OffsetNonalignmentFrom.NoExactFrom (fun k ↦ X (e k)) L
      (fun v ↦ label (fun k ↦ X (e k)) L (M.map (reindex X L e).toLinearMap) v ≠ 0) j := by
  intro k hkj u₁ u₂ v₁ v₂ hu₁ hu₂ hv₁ hv₂ hne
  exact h (e k) (fun he ↦ hkj (e.injective he)) u₁ u₂ v₁ v₂
    (active_pullback X L e M (j, u₁) hu₁) (active_pullback X L e M (j, u₂) hu₂)
    (active_pullback X L e M (k, v₁) hv₁) (active_pullback X L e M (k, v₂) hv₂) hne

end PaperP1.PhysicalWindowReindex
