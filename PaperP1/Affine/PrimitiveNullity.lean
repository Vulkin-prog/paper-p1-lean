module

public import PaperP1.Affine.RetainedNullity

/-! # A minimal effective relation has nullity bounded by every local rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveNullity

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

local instance finite_span (I : Finset ι) : FiniteDimensional 𝔽₂ (span S I) :=
  RetainedNullity.span_finite S I

theorem delete_bound (I : Finset ι) (i : ι) (hi : i ∈ I) :
    relativeNullityOn S I ≤ relativeNullityOn S (I.erase i) + Module.finrank 𝔽₂ (S i) := by
  have hfull := rank_add_nullity_on S I
  have herase := rank_add_nullity_on S (I.erase i)
  have hsum := sum_erase_add I (fun j ↦ Module.finrank 𝔽₂ (S j)) hi
  have hmono := Submodule.finrank_mono (span_mono S (erase_subset i I))
  change rank S (I.erase i) ≤ rank S I at hmono
  omega

theorem minimal_bound (I : Finset ι)
    (hproper : ∀ J : Finset ι, J ⊂ I → relativeNullityOn S J = 0) (i : ι) (hi : i ∈ I) :
    relativeNullityOn S I ≤ Module.finrank 𝔽₂ (S i) := by
  have h := delete_bound S I i hi
  rw [hproper (I.erase i) (erase_ssubset hi), zero_add] at h
  exact h

end PaperP1.PrimitiveNullity
