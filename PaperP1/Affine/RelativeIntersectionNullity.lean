module

public import PaperP1.Affine.MinimalRelativeRelations

/-! # Relative nullity is internal nullity plus the intersection with the old space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntersectionNullity

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]

theorem identity (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]
    (W : Submodule 𝔽₂ U) [Fintype W] (A : Finset ι) :
    MinimalRelativeRelations.nullity W S A = relativeNullityOn S A +
      Module.finrank 𝔽₂ ↥(W ⊓ span S A) := by
  let : FiniteDimensional 𝔽₂ W := Module.Finite.of_finite
  let : FiniteDimensional 𝔽₂ (span S A) := RetainedNullity.span_finite S A
  have hrel := MinimalRelativeRelations.dimension_identity W S A
  have hrank := rank_add_nullity_on S A
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq W (span S A)
  change Module.finrank 𝔽₂ (span S A) + relativeNullityOn S A = _ at hrank
  omega

theorem zero_of_direct (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]
    (W : Submodule 𝔽₂ U) [Fintype W] (A : Finset ι)
    (hzero : relativeNullityOn S A = 0) (hdis : Disjoint W (span S A)) :
    MinimalRelativeRelations.nullity W S A = 0 := by
  rw [identity, hzero, hdis.eq_bot, finrank_bot, add_zero]

end PaperP1.RelativeIntersectionNullity
