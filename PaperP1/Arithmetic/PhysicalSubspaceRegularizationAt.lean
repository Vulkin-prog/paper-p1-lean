module

public import PaperP1.Arithmetic.InjectivePhysicalRelationRegularization

/-! # Recovery regularization inside any prescribed physical subspace

All previously zeroed coordinates are preserved by the proved subspace inclusion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalSubspaceRegularizationAt

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ)
    (R : Submodule F₂ (code X L)) : AddCommGroup R := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) R

theorem uniform_subspace (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ 3 →
      ∀ (X : ι → ℕ) (L : ℕ), 1 ≤ L → ∀ R : Submodule F₂ (code X L),
      ∃ M : Submodule F₂ (code X L), M ≤ R ∧
        DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M 2 t ∧
        (Module.finrank F₂ R : ℝ) - η * L / 4 ≤ Module.finrank F₂ M ∧
        ∀ i, Function.Injective ((projection X L i).comp R.subtype) →
          Function.Injective ((projection X L i).comp M.subtype) := by
  obtain ⟨t, ht, hcost⟩ := SmallRecoveryParameter.exists_relative_cost 2 (by omega) η hη
  refine ⟨t, ht, ?_⟩
  intro ι _ _ hι X L hL R
  let ℓ := fun v ↦ (CoordinateForms.coordinateFamily (code X L) v).comp R.subtype
  obtain ⟨Q, hQ⟩ := DisjointRecoveryTheorem.disjoint_recovery_sharp (U := R) ℓ 2 t (by omega) ht
  let M := Q.map R.subtype
  have hdim : Module.finrank F₂ M = Module.finrank F₂ Q :=
    RecoveryImage.finrank_image R.subtype Subtype.val_injective Q
  have hcard : Fintype.card (ι × Fin (L + 1)) ≤ 3 * (L + 1) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hι
  have hbudget : 2 * (Fintype.card (ι × Fin (L + 1)) : ℝ) *
      DisjointRecoveryParameters.parameter 2 t ≤ η * L / 4 := by
    have hcardR : (Fintype.card (ι × Fin (L + 1)) : ℝ) ≤ ((3 * (L + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    calc
      _ ≤ 2 * ((3 * (L + 1) : ℕ) : ℝ) * DisjointRecoveryParameters.parameter 2 t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num))
          (DisjointRecoveryParameters.parameter_pos 2 t ht).le
      _ ≤ _ := hcost L hL
  have hcodim := hQ.1
  rw [Nat.cast_sub (Submodule.finrank_le Q)] at hcodim
  refine ⟨M, ?_, RecoveryImage.no_recovery_image R.subtype Subtype.val_injective _ Q 2 t hQ.2.1, ?_, ?_⟩
  · intro u hu
    obtain ⟨r, _hr, rfl⟩ := Submodule.mem_map.mp hu
    exact r.property
  · rw [hdim]
    linarith only [hcodim, hbudget]
  · intro i hinj
    exact RecoveryImage.projection_image_injective R.subtype Subtype.val_injective Q
      ((projection X L i).comp R.subtype) (projection X L i) rfl hinj

end PaperP1.PhysicalSubspaceRegularizationAt
