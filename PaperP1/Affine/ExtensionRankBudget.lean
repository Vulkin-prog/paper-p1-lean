module

public import PaperP1.Affine.RelationProjection

/-! # Exact rank gained when one effective block is added to a source family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExtensionRankBudget

open PaperP1.Affine

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι]
variable (S : Option ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def increment : ℕ := relativeNullity S - relativeNullity (fun i : ι ↦ S (some i))

theorem total_rank_identity :
    Module.finrank 𝔽₂ (⨆ i, S i : Submodule 𝔽₂ U) + increment S =
      Module.finrank 𝔽₂ (⨆ i : ι, S (some i) : Submodule 𝔽₂ U) + Module.finrank 𝔽₂ (S none) := by
  have hfull := relativeNullity_dimension_identity S
  have hold := relativeNullity_dimension_identity (fun i : ι ↦ S (some i))
  rw [Fintype.sum_option] at hfull
  have hinc := RelationProjection.projection_dimension_identity S
  dsimp [increment]
  omega

theorem increment_le_new_rank : increment S ≤ Module.finrank 𝔽₂ (S none) := by
  rw [increment, RelationProjection.nullity_increment]
  exact Submodule.finrank_le (LinearMap.range (RelationProjection.projection S none))

end PaperP1.ExtensionRankBudget
