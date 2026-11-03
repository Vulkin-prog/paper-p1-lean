module

public import PaperP1.Model.FiniteGoodChannelPartition
public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Model.DependentPairJointActivity

/-! # The literal nongood dependent pairs are covered by the height-five tail and finite exceptional sector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NongoodPairSeeds

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteGoodChannelPartition PaperP1.GoodEdgeCompression

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (H : ℝ) (N L : ℕ) (G : Finset ℕ) : Finset (Finset ℕ) :=
  DependentFamilySeeds.dependentFamilies G L 2 \ goodEdges H N L

theorem mem_families (H : ℝ) (N L : ℕ) (G e : Finset ℕ) :
    e ∈ families H N L G ↔ e ⊆ G ∧ e.card = 2 ∧ 0 < runRelativeNullity L e ∧ e ∉ goodEdges H N L := by
  simp only [families, mem_sdiff, DependentFamilySeeds.dependentFamilies, mem_filter, mem_powersetCard]
  tauto

theorem good_four_subset (N H L : ℕ) (hN : 2 ≤ N) (hlarge : 8 * (L + 1) < N) :
    good 4 N H L ⊆ goodEdges (H : ℝ) N L := by
  classical
  intro e he
  obtain ⟨hdep, hq, ab, hab, hp⟩ := good_data he
  obtain ⟨ha, hlt, hint, _hcop, hb, hb4⟩ := FiniteAlignedChannelCover.channel_data hab
  have hlead : Leading ab.1 ab.2 := by unfold Leading; omega
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hp
  obtain ⟨hx, hy, _hu, hprivate⟩ := PrivateChannelSources.mem_goodSources.mp hxy
  have hsmall : (ab.1 + ab.2) * (L + 1) < N :=
    (Nat.mul_le_mul_right (L + 1) (show ab.1 + ab.2 ≤ 8 by omega)).trans_lt hlarge
  have horder := PrivateChannelSources.good_sources_order hN hlt hsmall hxy
  have hnot : ¬Disjoint (squareClassSpace xy.1 L) (squareClassSpace xy.2 L) := by
    intro hd
    have hpos := (mem_filter.mp hdep).2
    rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ _ _ horder.ne,
      hd.eq_bot, finrank_bot] at hpos
    omega
  apply mem_image.mpr
  exact ⟨xy, mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩,
    hx, hy, horder, hq, hnot, ab.1, ab.2, hlead, hprivate⟩, rfl⟩

theorem cover (N L : ℕ) (hN : 2 ≤ N) (hlarge : 8 * (L + 1) < N)
    (G : Finset ℕ) (hG : G ⊆ dyadicBlock N) :
    families (8 * (L + 1) : ℕ) N L G ⊆
      weak 4 N (8 * (L + 1)) L ∪ exceptional 4 N (8 * (L + 1)) L := by
  intro e he
  obtain ⟨heG, hecard, hdep, hnot⟩ := (mem_families _ N L G e).mp he
  have heN : e ∈ DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2 :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨heG.trans hG, hecard⟩, hdep⟩
  rw [← FiniteGoodChannelPartition.cover 4 N (8 * (L + 1)) L] at heN
  rcases mem_union.mp heN with hgw | hex
  · rcases mem_union.mp hgw with hg | hw
    · exact False.elim (hnot (good_four_subset N (8 * (L + 1)) L hN hlarge hg))
    · exact mem_union_left _ hw
  · exact mem_union_right _ hex

theorem joint_bound (N L : ℕ) (hN : 2 ≤ N) (hL : 0 < L) (hlarge : 8 * (L + 1) < N)
    (G : Finset ℕ) (hG : G ⊆ dyadicBlock N) :
    (∑ e ∈ families (8 * (L + 1) : ℕ) N L G, infiniteJointMoment L e) ≤
      2 * (CompatibleActivitySplit.absolute L (weak 4 N (8 * (L + 1)) L) +
        CompatibleActivitySplit.absolute L (exceptional 4 N (8 * (L + 1)) L)) := by
  calc
    _ ≤ 2 * CompatibleActivitySplit.absolute L (families (8 * (L + 1) : ℕ) N L G) := by
      rw [CompatibleActivitySplit.absolute, mul_sum]
      apply sum_le_sum
      intro e he
      have hd := (mem_families _ N L G e).mp he
      exact DependentPairJointActivity.pointwise L hL e hd.2.1 hd.2.2.1
    _ ≤ 2 * CompatibleActivitySplit.absolute L
        (weak 4 N (8 * (L + 1)) L ∪ exceptional 4 N (8 * (L + 1)) L) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (cover N L hN hlarge G hG)
        (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (GraphStarWeights.sum_union_le_nonneg _ _ (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)) (by norm_num)

end PaperP1.NongoodPairSeeds
