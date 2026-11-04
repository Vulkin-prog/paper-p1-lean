module

public import PaperP1.Model.RetainedBoundaryPositiveMass
public import PaperP1.Model.DependentPairJointActivity
public import PaperP1.Model.CompatibleWindowOverlap
public import PaperP1.Probability.PositionalAllPairCost
public import PaperP1.Combinatorics.ClosePairs

/-! # The literal all-pair graph of companion T19.14

Its edges are exact contacts and strictly separated pairs of positive
relative nullity. This is a graph of original constraint spaces.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairDependencyGraph

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PositionalFiniteLaw PaperP1.PositionalPairDeletion PaperP1.PositionalAllPairCost

local instance allPairGraphDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def edges (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  (G.powersetCard 2).filter (fun e ↦ ∃ x y : ℕ, e = {x, y} ∧ x < y ∧
    (y = x + L ∨ (x + L < y ∧ 0 < runRelativeNullity L e)))

theorem subset_pairs (G : Finset ℕ) (L : ℕ) : edges G L ⊆ G.powersetCard 2 := filter_subset _ _

theorem edge_data (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (he : e ∈ edges G L) :
    e ⊆ G ∧ e.card = 2 := mem_powersetCard.mp (subset_pairs G L he)

theorem good_subset {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    GoodEdgeCompression.goodEdges H N L ⊆ edges (RegularStarts.regularStarts N L) L := by
  intro e he
  have heG := RetainedGoodEdges.good_pair_regular hN e he
  have hecard := RetainedGoodEdges.good_pair_card H N L e he
  have hdep := RetainedGoodEdges.good_pair_positive H N L e he
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨_hx, _hy, hlt, hq, _hnd, _hrest⟩ := (mem_filter.mp hxy).2
  have hsep := CompatibleWindowOverlap.compatible_pair_separated hlt.ne hL hq
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨heG, hecard⟩, xy.1, xy.2, rfl, hlt, ?_⟩
  by_cases heq : xy.2 = xy.1 + L
  · exact Or.inl heq
  · exact Or.inr ⟨by omega, hdep⟩

theorem bad_cover (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    edges G L \ GoodEdgeCompression.goodEdges H N L ⊆
      ClosePairs.pairs G L ∪ NongoodPairSeeds.families H N L G := by
  intro e he
  obtain ⟨heF, hnot⟩ := mem_sdiff.mp he
  have hedata := edge_data G L e heF
  obtain ⟨_hp, x, y, heq, hxy, hcase⟩ := mem_filter.mp heF
  rcases hcase with hcontact | ⟨_hsep, hdep⟩
  · apply mem_union_left
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr hedata, x, ?_, y, ?_, hxy, hcontact.le⟩
    · rw [heq]
      exact mem_insert_self _ _
    · rw [heq]
      exact mem_insert_of_mem (mem_singleton_self _)
  · apply mem_union_right
    exact (NongoodPairSeeds.mem_families H N L G e).mpr ⟨hedata.1, hedata.2, hdep, hnot⟩

theorem bad_mass_bound (H : ℝ) (N L : ℕ) (hL : 0 < L) (G : Finset ℕ) :
    (∑ e ∈ edges G L \ GoodEdgeCompression.goodEdges H N L, infiniteJointMoment L e) ≤
      (∑ e ∈ ClosePairs.pairs G L, infiniteJointMoment L e) +
        2 * ∑ e ∈ G.powersetCard 2 \ GoodEdgeCompression.goodEdges H N L,
          |infiniteCenteredCoefficient L e| := by
  have hdep : (∑ e ∈ NongoodPairSeeds.families H N L G, infiniteJointMoment L e) ≤
      2 * ∑ e ∈ G.powersetCard 2 \ GoodEdgeCompression.goodEdges H N L,
        |infiniteCenteredCoefficient L e| := by
    calc
      _ ≤ ∑ e ∈ NongoodPairSeeds.families H N L G, 2 * |infiniteCenteredCoefficient L e| := by
        apply sum_le_sum
        intro e he
        have hd := (NongoodPairSeeds.mem_families H N L G e).mp he
        exact DependentPairJointActivity.pointwise L hL e hd.2.1 hd.2.2.1
      _ = 2 * ∑ e ∈ NongoodPairSeeds.families H N L G, |infiniteCenteredCoefficient L e| := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg
        (fun e he ↦ by
          have hd := (NongoodPairSeeds.mem_families H N L G e).mp he
          exact mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨hd.1, hd.2.1⟩, hd.2.2.2⟩)
        (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))) (by norm_num)
  exact ((sum_le_sum_of_subset_of_nonneg (bad_cover H N L G)
    (fun e _ _ ↦ infiniteJointMoment_nonneg L e)).trans
    (GraphStarWeights.sum_union_le_nonneg _ _ (infiniteJointMoment L) (infiniteJointMoment_nonneg L))).trans
      (add_le_add le_rfl hdep)

theorem retained_no_edge (G : Finset ℕ) (L : ℕ) (v : Configuration ℕ) :
    activeEdges (edges G L) (isolate (edges G L) (restrict G v)) = ∅ :=
  isolate_no_active _ _ (fun e he ↦ card_pos.mp (by rw [(edge_data G L e he).2]; omega))

end PaperP1.AllPairDependencyGraph
