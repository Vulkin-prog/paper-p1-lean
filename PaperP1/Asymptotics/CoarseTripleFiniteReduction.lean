module

public import PaperP1.Asymptotics.StrongAlignedInteriorEdges
public import PaperP1.Model.CoarseTriplePairSeeds
public import PaperP1.Model.TriplePairDependence

/-! # An exhaustive actual triple cover by isolated vertices, small pair seeds and two finite-channel edges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseTripleFiniteReduction

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_cover (θ : ℝ) (hθ : 0 < θ) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : Finset ℕ,
      T ⊆ dyadicBlock N → T.card = 3 →
      (∃ x ∈ T, ∀ y ∈ T.erase x, Disjoint (squareClassSpace x L) (squareClassSpace y L)) ∨
      (∃ e ∈ CoarseTriplePairSeeds.pairs N L θ, e ⊆ T) ∨
      2 ≤ ((FiniteInteriorUnitEdges.edges N L Q).filter fun e ↦ e ⊆ T).card := by
  classical
  obtain ⟨Q, hQ, h⟩ := StrongAlignedInteriorEdges.uniform_edges θ hθ
  refine ⟨Q, hQ, fun C ↦ ?_⟩
  obtain ⟨N₀, hN₀, h⟩ := h C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband T hTG hT
  by_cases hiso : ∃ x ∈ T, ∀ y ∈ T.erase x,
      Disjoint (squareClassSpace x L) (squareClassSpace y L)
  · exact Or.inl hiso
  right
  by_cases hbad : ∃ e ∈ CoarseTriplePairSeeds.pairs N L θ, e ⊆ T
  · exact Or.inl hbad
  right
  have htwo := (TriplePairDependence.isolated_or_two L T hT).resolve_left hiso
  apply htwo.trans (card_le_card ?_)
  intro e he
  obtain ⟨heT, hdep⟩ := mem_filter.mp he
  obtain ⟨heSub, heCard⟩ := mem_powersetCard.mp heT
  have heN : e ∈ DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2 :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨heSub.trans hTG, heCard⟩, hdep⟩
  have hnot (hp : e ∈ WeakPairActivity.pairs (dyadicBlock N) L θ ∨
      e ∈ AllAlignedPairs.nonaligned N L ∨ e ∈ BoundaryAlignedPairs.channel N L 1 1 ∨
      e ∈ BoundaryAlignedPairs.channel N L 1 2) : False :=
    hbad ⟨e, (CoarseTriplePairSeeds.mem_pairs N L θ e).mpr ⟨heN, hp⟩, heSub⟩
  have heAligned : e ∈ AllAlignedPairs.families N L := by
    by_contra hn
    exact hnot (Or.inr (Or.inl (mem_sdiff.mpr
      ⟨mem_powersetCard.mpr ⟨heSub.trans hTG, heCard⟩, hn⟩)))
  obtain ⟨_heN, x, y, heq, hxy, halign⟩ := mem_filter.mp heAligned
  have hx : x ∈ dyadicBlock N := (heSub.trans hTG) (by rw [heq]; simp)
  have hy : y ∈ dyadicBlock N := (heSub.trans hTG) (by rw [heq]; simp)
  have hlarge : θ * L < (runRelativeNullity L e : ℝ) := by
    apply lt_of_not_ge
    intro hle
    exact hnot (Or.inl (mem_filter.mpr ⟨heN, Or.inl hle⟩))
  have hnull : runRelativeNullity L e = Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) := by
    rw [heq, runRelativeNullity]
    exact RetainedNullity.nullity_pair_eq_intersection _ x y hxy.ne
  rw [hnull] at hlarge
  have hOne : ({x, y} : Finset ℕ) ∉ BoundaryAlignedPairs.channel N L 1 1 := by
    intro hm
    exact hnot (Or.inr (Or.inr (Or.inl (heq ▸ hm))))
  have hTwo : ({x, y} : Finset ℕ) ∉ BoundaryAlignedPairs.channel N L 1 2 := by
    intro hm
    exact hnot (Or.inr (Or.inr (Or.inr (heq ▸ hm))))
  have hinter := h N hN L hband x y hx hy hxy hlarge halign hOne hTwo
  rw [← heq] at hinter
  exact mem_filter.mpr ⟨hinter, heSub⟩

end PaperP1.CoarseTripleFiniteReduction
