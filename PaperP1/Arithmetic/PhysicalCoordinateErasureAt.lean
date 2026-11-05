module

public import PaperP1.Arithmetic.ActivePhysicalPrimeGroups
public import PaperP1.Arithmetic.OffsetNonalignmentOn
public import PaperP1.Coding.CoordinateErasureRank
public import PaperP1.Coding.RecoveryImage

/-! # Erasing prescribed physical positions preserves every injective block projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalCoordinateErasureAt

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ActivePhysicalPrimeGroups

variable {ι : Type*} [Fintype ι]

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup (X : ι → ℕ) (L : ℕ) (R : Submodule F₂ (code X L)) : AddCommGroup R := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) R

theorem exists_erasure (X : ι → ℕ) (L : ℕ) (R : Submodule F₂ (code X L))
    (D : Finset (ι × Fin (L + 1))) :
    ∃ P : Submodule F₂ (code X L), P ≤ R ∧
      Module.finrank F₂ R ≤ D.card + Module.finrank F₂ P ∧
      (∀ u : P, ∀ v ∈ D, u.val.val v = 0) ∧
      ∀ i, Function.Injective ((projection X L i).comp R.subtype) →
        Function.Injective ((projection X L i).comp P.subtype) := by
  let Z := CoordinateForms.zeroCoordinates (U := R) (label X L R) D
  let P := Z.map R.subtype
  have hdim : Module.finrank F₂ P = Module.finrank F₂ Z :=
    RecoveryImage.finrank_image R.subtype Subtype.val_injective Z
  have hcost := CoordinateErasureRank.dimension_cost (U := R) (label X L R) D
  change Module.finrank F₂ R ≤ D.card + Module.finrank F₂ Z at hcost
  refine ⟨P, ?_, by omega, ?_, ?_⟩
  · intro u hu
    obtain ⟨r, _hr, rfl⟩ := Submodule.mem_map.mp hu
    exact r.property
  · intro u v hv
    obtain ⟨r, hr, he⟩ := Submodule.mem_map.mp u.property
    have hz : r.val.val v = 0 := hr v hv
    change R.subtype r = u.val at he
    rw [← he]
    exact hz
  · intro i hinj
    exact RecoveryImage.projection_image_injective R.subtype Subtype.val_injective Z
      ((projection X L i).comp R.subtype) (projection X L i) rfl hinj

end PaperP1.PhysicalCoordinateErasureAt
