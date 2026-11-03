module

public import PaperP1.Affine.PrimitiveRelations

/-! # Every coordinate projection is injective on a minimal relation kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveCoordinateProjection

open Finset PaperP1.Affine

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]

abbrev Kernel (S : κ → Submodule 𝔽₂ U) (I : Finset κ) :=
  LinearMap.ker (relationAddition (fun i : I ↦ S i.val))

def projection (S : κ → Submodule 𝔽₂ U) (I : Finset κ) (i : I) : Kernel S I →ₗ[𝔽₂] S i.val :=
  (LinearMap.proj i).comp (Kernel S I).subtype

theorem injective (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (I : Finset κ)
    (hproper : ∀ J : Finset κ, J ⊂ I → relativeNullityOn S J = 0) (i : I) :
    Function.Injective (projection S I i) := by
  classical
  apply (injective_iff_map_eq_zero (projection S I i)).mpr
  intro r hri
  have hs0 : relationAddition (fun j : I ↦ S j.val) r.val = 0 := r.property
  have hsi : r.val i = 0 := hri
  let J := I.erase i.val
  have hJI : J ⊆ I := erase_subset _ _
  let w : (j : J) → S j.val := fun j ↦ r.val ⟨j.val, hJI j.property⟩
  have hext : subfamilyExtend S hJI w = r.val := by
    funext j
    by_cases hji : j.val = i.val
    · have hji' : j = i := Subtype.ext hji
      subst j
      have hiJ : i.val ∉ J := by simp [J]
      change (if h : i.val ∈ J then w ⟨i.val, h⟩ else 0) = r.val i
      rw [dite_eq_right hiJ]
      exact hsi.symm
    · have hjJ : j.val ∈ J := mem_erase.mpr ⟨hji, j.property⟩
      change (if h : j.val ∈ J then w ⟨j.val, h⟩ else 0) = r.val j
      rw [dite_eq_left hjJ]
  have hrestricted : relationAddition (fun j : J ↦ S j.val) w = 0 := by
    have hsum := relationAddition_subfamilyExtend S hJI w
    rw [hext] at hsum
    exact hsum.symm.trans hs0
  have hinj := (PaperP1.CompressedBlocks.direct_family_iff_zero_nullity S J).mpr
    (hproper J (erase_ssubset i.property))
  have hwzero : w = 0 := hinj (hrestricted.trans (map_zero _).symm)
  apply Subtype.ext
  change r.val = 0
  rw [← hext, hwzero, map_zero]

theorem finrank_range (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)] (I : Finset κ)
    (hproper : ∀ J : Finset κ, J ⊂ I → relativeNullityOn S J = 0) (i : I) :
    Module.finrank 𝔽₂ (LinearMap.range (projection S I i)) = relativeNullityOn S I := by
  have h := (projection S I i).finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr (injective S I hproper i), finrank_bot, add_zero] at h
  exact h

end PaperP1.PrimitiveCoordinateProjection
