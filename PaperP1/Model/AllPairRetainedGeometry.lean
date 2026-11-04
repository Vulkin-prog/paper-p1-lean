module

public import PaperP1.Model.AllPairDependencyGraph
public import PaperP1.Model.PositionalDeletedFields

/-! # Retained original spaces are pairwise direct and strictly separated

This pointwise statement does not assert independence of the filtered
indicators or eliminate dependencies of order three or more.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairRetainedGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalAllPairCost

theorem retained_mem (G : Finset ℕ) (L : ℕ) (v : Configuration ℕ) (x : ℕ)
    (hx : 0 < isolate (AllPairDependencyGraph.edges G L) (restrict G v) x) : x ∈ G := by
  have hp := hx.trans_le (isolate_le (AllPairDependencyGraph.edges G L) (restrict G v) x)
  by_contra hn
  have hz : restrict G v x = 0 := by
    simp only [PositionalAllPairCost.restrict, Finsupp.filter_apply, ite_eq_right hn]
  rw [hz] at hp
  omega

theorem retained_le (G : Finset ℕ) (L : ℕ) (v : Configuration ℕ) (x : ℕ) :
    isolate (AllPairDependencyGraph.edges G L) (restrict G v) x ≤ v x :=
  (isolate_le _ _ x).trans (restrict_le G v x)

theorem retained_pair_absent (G : Finset ℕ) (L : ℕ) (v : Configuration ℕ) (x y : ℕ)
    (hx : 0 < isolate (AllPairDependencyGraph.edges G L) (restrict G v) x)
    (hy : 0 < isolate (AllPairDependencyGraph.edges G L) (restrict G v) y) :
    ({x, y} : Finset ℕ) ∉ AllPairDependencyGraph.edges G L := by
  classical
  intro he
  have ha : ({x, y} : Finset ℕ) ∈ activeEdges (AllPairDependencyGraph.edges G L)
      (isolate (AllPairDependencyGraph.edges G L) (restrict G v)) := by
    apply mem_filter.mpr
    refine ⟨he, ?_⟩
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hx
    · rw [mem_singleton.mp hz]
      exact hy
  rw [AllPairDependencyGraph.retained_no_edge] at ha
  exact notMem_empty _ ha

theorem retained_original_active (H G : Finset ℕ) (hGH : G ⊆ H) (L : ℕ)
    (ω : InfiniteSample) (x : ℕ)
    (hx : 0 < isolate (AllPairDependencyGraph.edges G L)
      (restrict G (configuration H (fun x ↦ infiniteStartIndicator x L) ω)) x) :
    infiniteStartIndicator x L ω = true := by
  have hxG := retained_mem G L _ x hx
  have hp := hx.trans_le (retained_le G L _ x)
  rw [PositionalGrid.configuration_apply_mem H (fun x ↦ infiniteStartIndicator x L) ω ⟨x, hGH hxG⟩] at hp
  cases hj : infiniteStartIndicator x L ω <;> simp only [hj, Bool.toNat_false, Bool.toNat_true] at hp ⊢
  omega

theorem retained_pair_geometry (H G : Finset ℕ) (hGH : G ⊆ H) (L : ℕ)
    (ω : InfiniteSample) (x y : ℕ) (hxy : x < y)
    (hx : 0 < isolate (AllPairDependencyGraph.edges G L)
      (restrict G (configuration H (fun x ↦ infiniteStartIndicator x L) ω)) x)
    (hy : 0 < isolate (AllPairDependencyGraph.edges G L)
      (restrict G (configuration H (fun x ↦ infiniteStartIndicator x L) ω)) y) :
    x + L < y ∧ Disjoint (squareClassSpace x L) (squareClassSpace y L) := by
  classical
  let v := configuration H (fun x ↦ infiniteStartIndicator x L) ω
  have hxG := retained_mem G L v x hx
  have hyG := retained_mem G L v y hy
  have hsep := RunSeparation.infiniteStartIndicator_separated ω
    (retained_original_active H G hGH L ω x hx) (retained_original_active H G hGH L ω y hy) hxy
  have hnot := retained_pair_absent G L v x y hx hy
  have hpair : ({x, y} : Finset ℕ) ∈ G.powersetCard 2 :=
    mem_powersetCard.mpr ⟨insert_subset_iff.mpr ⟨hxG, singleton_subset_iff.mpr hyG⟩, card_pair hxy.ne⟩
  have hstrict : x + L < y := by
    by_contra hn
    have heq : y = x + L := by omega
    exact hnot (mem_filter.mpr ⟨hpair, x, y, rfl, hxy, Or.inl heq⟩)
  have hzero : runRelativeNullity L {x, y} = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hnot (mem_filter.mpr ⟨hpair, x, y, rfl, hxy, Or.inr ⟨hstrict, hpos⟩⟩)
  rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ x y hxy.ne] at hzero
  exact ⟨hstrict, disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hzero)⟩

end PaperP1.AllPairRetainedGeometry
