module

public import PaperP1.Affine.SmallPrimePairConstraints
public import PaperP1.Model.FreeComponentRank
public import PaperP1.Model.CompatibleNullityBound
public import PaperP1.Affine.RetainedNullity

/-! # The full value kernel is bounded by the actual free large-prime components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawPairRelationRank

open PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeOccurrences PaperP1.LargePrimeGraph
  PaperP1.LargePrimeGraphResolution PaperP1.FreeComponentRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def fullRank (x y L : ℕ) : ℕ := Module.finrank F₂ (LinearMap.ker (pairVertexParityMap x y L))

theorem kernel_le_large (x y L : ℕ) :
    LinearMap.ker (pairVertexParityMap x y L) ≤ largePrimeSolution x y L := by
  intro w hw
  apply mem_largePrimeSolution_iff_boundary_prime_equations.mpr
  intro p _hp
  rw [← pairVertexParityMap_coord, LinearMap.mem_ker.mp hw, Finsupp.zero_apply]

theorem rank_le_large (x y L : ℕ) : fullRank x y L ≤ Module.finrank F₂ (largePrimeSolution x y L) :=
  Submodule.finrank_mono (kernel_le_large x y L)

theorem rank_le_components {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    fullRank x y L ≤ defectiveVertexCount x y L + nontrivialComponentCount x y L := by
  rw [← finrank_largePrimeSolution_eq_defective_add_components hx hy]
  exact rank_le_large x y L

theorem complete_le_full (x y L : ℕ) :
    Module.finrank F₂ (completeRelationCode x y L) ≤ fullRank x y L :=
  Submodule.finrank_mono inf_le_left

theorem intersection_le_full (x y L : ℕ) : pairIntersectionRank x y L ≤ fullRank x y L := by
  have hc := complete_le_full x y L
  rw [finrank_completeRelationCode] at hc
  dsimp [pairIntersectionRank]
  omega

theorem relative_le_full (x y L : ℕ) :
    Model.InfiniteStarts.runRelativeNullity L {x, y} ≤ fullRank x y L := by
  classical
  by_cases hxy : x = y
  · subst y
    simp only [Finset.pair_eq_singleton, Model.InfiniteStarts.runRelativeNullity,
      RetainedNullity.nullity_singleton]
    exact Nat.zero_le _
  · rw [Model.InfiniteStarts.runRelativeNullity,
      RetainedNullity.nullity_pair_eq_intersection _ _ _ hxy]
    exact intersection_le_full x y L

end PaperP1.RawPairRelationRank
