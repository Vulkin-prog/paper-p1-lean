module

public import PaperP1.Affine.Subfamilies

/-! # A direct pair has zero effective relative nullity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open Finset

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

theorem relativeNullityOn_pair_eq_zero (x y : κ) (hxy : x ≠ y) (hdisj : Disjoint (S x) (S y)) :
    relativeNullityOn S {x, y} = 0 := by
  classical
  have hsup : (⨆ i : ({x, y} : Finset κ), S i.val) = S x ⊔ S y := by
    apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      obtain h | h := mem_insert.mp i.property
      · simpa only [h] using (le_sup_left : S x ≤ S x ⊔ S y)
      · simpa only [mem_singleton.mp h] using (le_sup_right : S y ≤ S x ⊔ S y)
    · exact sup_le (le_iSup_of_le (⟨x, by simp⟩ : ({x, y} : Finset κ)) le_rfl)
        (le_iSup_of_le (⟨y, by simp⟩ : ({x, y} : Finset κ)) le_rfl)
  have hsum : (∑ i : ({x, y} : Finset κ), Module.finrank 𝔽₂ (S i.val)) =
      Module.finrank 𝔽₂ (S x) + Module.finrank 𝔽₂ (S y) := by
    rw [sum_coe_sort ({x, y} : Finset κ) (fun z ↦ Module.finrank 𝔽₂ (S z))]
    simp only [sum_pair hxy]
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq (S x) (S y)
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hrank
  rw [relativeNullityOn, relativeNullity_eq_dimension_deficit, hsum, hsup, hrank, Nat.sub_self]

end PaperP1.Affine
