module

public import PaperP1.Model.IncidentPairMass
public import PaperP1.Probability.PositionalInsertedPair
public import PaperP1.Combinatorics.GraphStarWeights

/-! # The sites of edges touching a pair are controlled by actual one-source targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgeTouchingMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance touchingMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def neighbors (G : Finset ℕ) (E : Finset (Finset ℕ)) (x : ℕ) : Finset ℕ :=
  G.filter (fun y ↦ y ≠ x ∧ ({x, y} : Finset ℕ) ∈ E)

theorem neighbors_target_subset (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ))
    (hE : ∀ e ∈ E, 0 < runRelativeNullity L e) (x : ℕ) :
    neighbors G E x ⊆ WindowTargetHosts.targets G L {x} := by
  intro y hy
  obtain ⟨hyG, hyx, heE⟩ := mem_filter.mp hy
  have hpos := hE _ heE
  rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ x y hyx.symm] at hpos
  apply mem_filter.mpr
  refine ⟨mem_sdiff.mpr ⟨hyG, by simpa only [mem_singleton] using hyx⟩, ?_⟩
  have hspan : SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {x} = squareClassSpace x L := by
    simp [SubspaceFamilyRank.span]
  change squareClassSpace y L ⊓ SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {x} ≠ ⊥
  rw [hspan, inf_comm]
  intro hbot
  rw [hbot, finrank_bot] at hpos
  omega

theorem touching_cover (G : Finset ℕ) (E : Finset (Finset ℕ)) (e : Finset ℕ)
    (hE : ∀ f ∈ E, f ⊆ G ∧ f.card = 2) :
    PositionalInsertedPair.touchingVertices E e ⊆ e ∪ e.biUnion (neighbors G E) := by
  intro z hz
  obtain ⟨f, hfE, htouch, hzf⟩ := (PositionalInsertedPair.mem_touching E e z).mp hz
  obtain ⟨x, hxf, hxe⟩ := not_disjoint_iff.mp htouch
  by_cases hzx : z = x
  · subst z
    exact mem_union_left _ hxe
  · have hxz : x ≠ z := fun h ↦ hzx h.symm
    have hpair : ({x, z} : Finset ℕ) = f := eq_of_subset_of_card_le
      (insert_subset_iff.mpr ⟨hxf, singleton_subset_iff.mpr hzf⟩)
      (by rw [card_pair hxz, (hE f hfE).2])
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨x, hxe, mem_filter.mpr ⟨(hE f hfE).1 hzf, hzx, ?_⟩⟩
    rwa [hpair]

theorem mass_bound (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ)) (e : Finset ℕ)
    (hE : ∀ f ∈ E, f ⊆ G ∧ f.card = 2 ∧ 0 < runRelativeNullity L f)
    (r : ℕ → ℝ) (hr : ∀ x, 0 ≤ r x) (hrp : ∀ x ∈ G, r x ≤ infiniteMarginal x L) :
    (∑ z ∈ PositionalInsertedPair.touchingVertices E e, r z) ≤
      (∑ x ∈ e, r x) + ∑ x ∈ e, ∑ y ∈ WindowTargetHosts.targets G L {x}, infiniteMarginal y L := by
  have hcover := touching_cover G E e (fun f hf ↦ ⟨(hE f hf).1, (hE f hf).2.1⟩)
  calc
    _ ≤ ∑ z ∈ e ∪ e.biUnion (neighbors G E), r z :=
      sum_le_sum_of_subset_of_nonneg hcover (fun z _ _ ↦ hr z)
    _ ≤ (∑ x ∈ e, r x) + ∑ z ∈ e.biUnion (neighbors G E), r z :=
      GraphStarWeights.sum_union_le_nonneg _ _ r hr
    _ ≤ (∑ x ∈ e, r x) + ∑ x ∈ e, ∑ y ∈ neighbors G E x, r y :=
      add_le_add le_rfl (GraphStarWeights.sum_biUnion_le_nonneg e (neighbors G E) r hr)
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro x _hx
      calc
        _ ≤ ∑ y ∈ neighbors G E x, infiniteMarginal y L :=
          sum_le_sum (fun y hy ↦ hrp y (mem_filter.mp hy).1)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg
          (neighbors_target_subset G L E (fun f hf ↦ (hE f hf).2.2) x)
          (fun y _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg y L)

end PaperP1.GoodEdgeTouchingMass
