module

public import PaperP1.Algebra.EvenPreimageRank

/-! # Projection can only enlarge the preimage budget for a genuine intersection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectedPreimageRank

variable {K V W Z : Type*} [DivisionRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]

theorem intersection_le (f : V →ₗ[K] W) (g : W →ₗ[K] Z)
    (S : Submodule K W) (T : Submodule K Z) (hST : S.map g ≤ T) :
    Module.finrank K ↥(LinearMap.range f ⊓ S) ≤ Module.finrank K (T.comap (g.comp f)) := by
  have hmap := Submodule.finrank_map_le f (S.comap f)
  rw [Submodule.map_comap_eq] at hmap
  have hsub : S.comap f ≤ T.comap (g.comp f) := by
    intro v hv
    exact hST ⟨f v, hv, rfl⟩
  exact hmap.trans (Submodule.finrank_mono hsub)

end PaperP1.ProjectedPreimageRank
