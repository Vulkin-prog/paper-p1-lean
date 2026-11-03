module

public import PaperP1.Arithmetic.PhysicalWindowRelations

/-! # Physical representatives of any injectively projected effective relation subspace -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalRelationSections

open PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations

variable {ι : Type*} [Fintype ι]

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance effectiveAddCommGroup (X : ι → ℕ) (L : ℕ) : AddCommGroup (EffectiveKernel X L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := (i : ι) → squareClassSpace (X i) L) (EffectiveKernel X L)
local instance effectiveSubspaceAddCommGroup (X : ι → ℕ) (L : ℕ)
    (R : Submodule F₂ (EffectiveKernel X L)) : AddCommGroup R := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := EffectiveKernel X L) R

theorem section_subspace (X : ι → ℕ) (L : ℕ) (R : Submodule F₂ (EffectiveKernel X L))
    (hinj : ∀ i, Function.Injective ((effectiveProjection X L i).comp R.subtype)) :
    ∃ P : Submodule F₂ (code X L), Module.finrank F₂ P = Module.finrank F₂ R ∧
      ∀ i, Function.Injective ((projection X L i).comp P.subtype) := by
  let : FiniteDimensional F₂ (EffectiveKernel X L) :=
    FiniteDimensional.of_surjective (toEffective X L) (toEffective_surjective X L)
  obtain ⟨σ, hσ⟩ := (toEffective X L).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (toEffective_surjective X L))
  have hσfun (r : EffectiveKernel X L) : toEffective X L (σ r) = r := LinearMap.congr_fun hσ r
  have hσinj : Function.Injective σ := by
    intro r s he
    exact (hσfun r).symm.trans ((congrArg (toEffective X L) he).trans (hσfun s))
  let f := σ.comp R.subtype
  have hf : Function.Injective f := hσinj.comp Subtype.val_injective
  have hproj (i : ι) : Function.Injective ((projection X L i).comp f) := by
    intro r s he
    apply hinj i
    have hsel : localSelection X L i (f r) = localSelection X L i (f s) := Subtype.ext he
    have hval := congrArg ((evenSquareClassMap (X i) L).rangeRestrict) hsel
    change effectiveProjection X L i (toEffective X L (σ r.val)) =
      effectiveProjection X L i (toEffective X L (σ s.val)) at hval
    change effectiveProjection X L i r.val = effectiveProjection X L i s.val
    simpa only [hσfun] using hval
  let P := LinearMap.range f
  refine ⟨P, LinearMap.finrank_range_of_inj hf, ?_⟩
  intro i r s he
  obtain ⟨u, hu⟩ := r.property
  obtain ⟨v, hv⟩ := s.property
  have huv : u = v := hproj i (by
    change projection X L i (f u) = projection X L i (f v)
    rw [hu, hv]
    exact he)
  apply Subtype.ext
  exact hu.symm.trans ((congrArg f huv).trans hv)

end PaperP1.PhysicalRelationSections
