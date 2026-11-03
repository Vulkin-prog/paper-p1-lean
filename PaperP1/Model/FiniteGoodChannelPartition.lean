module

public import PaperP1.Model.FiniteAlignedChannelCover
public import PaperP1.Model.AbsoluteActivityDecomposition

/-! # A disjoint actual weak/exceptional/good partition for any fixed channel cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGoodChannelPartition

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.DependentFamilySeeds PaperP1.FiniteAlignedChannelCover PaperP1.PrivateChannelSources

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def good (Q N H L : ℕ) : Finset (Finset ℕ) :=
  (dependentFamilies (dyadicBlock N) L 2).filter fun e ↦
    0 < infiniteJointMoment L e ∧ e ∈ privatePairs Q N H L

def weak (Q N H L : ℕ) : Finset (Finset ℕ) :=
  (dependentFamilies (dyadicBlock N) L 2 ∩ AlignedChannelFamilies.families N L (Q + 1)) \ good Q N H L

def exceptional (Q N H L : ℕ) : Finset (Finset ℕ) :=
  dependentFamilies (dyadicBlock N) L 2 \ (good Q N H L ∪ weak Q N H L)

def incompatible (N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 2).filter fun e ↦ infiniteJointMoment L e = 0

def exceptionalClasses (Q N H L i : ℕ) : Finset (Finset ℕ) :=
  if i = 0 then AllAlignedPairs.nonaligned N L else
  if i = 1 then BoundaryAlignedPairs.channel N L 1 1 else
  if i = 2 then BoundaryAlignedPairs.channel N L 1 2 else
  if i = 3 then AlignedChannelFamilies.zeroFamilies N L else
  if i = 4 then defectivePairs Q N H L else incompatible N L

theorem good_subset (Q N H L : ℕ) : good Q N H L ⊆ dependentFamilies (dyadicBlock N) L 2 := filter_subset _ _

theorem disjoint_classes (Q N H L : ℕ) :
    Disjoint (good Q N H L) (weak Q N H L) ∧
      Disjoint (good Q N H L) (exceptional Q N H L) ∧
      Disjoint (weak Q N H L) (exceptional Q N H L) := by
  refine ⟨disjoint_left.mpr (fun _ hg hw ↦ (mem_sdiff.mp hw).2 hg),
    disjoint_left.mpr (fun _ hg he ↦ (mem_sdiff.mp he).2 (mem_union_left _ hg)),
    disjoint_left.mpr (fun _ hw he ↦ (mem_sdiff.mp he).2 (mem_union_right _ hw))⟩

theorem cover (Q N H L : ℕ) :
    (good Q N H L ∪ weak Q N H L) ∪ exceptional Q N H L = dependentFamilies (dyadicBlock N) L 2 := by
  have hsub : good Q N H L ∪ weak Q N H L ⊆ dependentFamilies (dyadicBlock N) L 2 := by
    intro e he
    rcases mem_union.mp he with hg | hw
    · exact good_subset Q N H L hg
    · exact (mem_inter.mp (mem_sdiff.mp hw).1).1
  exact union_sdiff_of_subset hsub

theorem good_data {Q N H L : ℕ} {e : Finset ℕ} (he : e ∈ good Q N H L) :
    e ∈ dependentFamilies (dyadicBlock N) L 2 ∧ 0 < infiniteJointMoment L e ∧
      ∃ ab ∈ channels Q, e ∈ PrivateChannelActivity.pairs N H ab.1 ab.2 L := by
  obtain ⟨hdep, hq, hp⟩ := mem_filter.mp he
  exact ⟨hdep, hq, mem_biUnion.mp hp⟩

theorem good_compression {Q N H L : ℕ} (hN : 2 ≤ N) {e : Finset ℕ}
    (he : e ∈ good Q N H L) :
    ∃ ab ∈ channels Q, e ∈ PrivateChannelActivity.pairs N H ab.1 ab.2 L ∧
      ∃ x y : ℕ, e = {x, y} ∧ GoodEdgeCompression.Conclusion ab.1 ab.2 x y L := by
  obtain ⟨_hdep, _hq, ab, hab, hp⟩ := good_data he
  obtain ⟨ha, hlt, _hint, hcop, _hb, _hbQ⟩ := channel_data hab
  refine ⟨ab, hab, hp, ?_⟩
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hp
  obtain ⟨hx, hy, hu, hprivate⟩ := mem_goodSources.mp hxy
  refine ⟨xy.1, xy.2, rfl, ?_⟩
  exact GoodEdgeCompression.finite_compression ha (ha.trans hlt) hcop hlt.le
    (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1)
    (card_pos.mp (by omega)) hprivate.private

theorem exceptional_nonzero_cover {Q N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hheight : Q ≤ (L + 1) ^ 3) (hlarge : 2 * (L + 1) ^ 4 < N)
    {e : Finset ℕ} (he : e ∈ exceptional Q N H L) (hn : infiniteCenteredCoefficient L e ≠ 0) :
    ∃ i ∈ range 6, e ∈ exceptionalClasses Q N H L i := by
  obtain ⟨hdep, hnot⟩ := mem_sdiff.mp he
  have heN := (mem_filter.mp hdep).1
  have hng : e ∉ good Q N H L := fun hg ↦ hnot (mem_union_left _ hg)
  have hnw : e ∉ weak Q N H L := fun hw ↦ hnot (mem_union_right _ hw)
  by_cases haligned : e ∈ AllAlignedPairs.families N L
  · rcases FiniteAlignedChannelCover.nonzero_cover hN hL hheight hlarge haligned hn with h1 | h2 | hp | hd | hz | ht
    · exact ⟨1, by decide, by simpa [exceptionalClasses] using h1⟩
    · exact ⟨2, by decide, by simpa [exceptionalClasses] using h2⟩
    · by_cases hq : 0 < infiniteJointMoment L e
      · exact False.elim (hng (mem_filter.mpr ⟨hdep, hq, hp⟩))
      · have hzero : infiniteJointMoment L e = 0 := le_antisymm (le_of_not_gt hq) (infiniteJointMoment_nonneg L e)
        refine ⟨5, by decide, ?_⟩
        change e ∈ incompatible N L
        exact mem_filter.mpr ⟨heN, hzero⟩
    · exact ⟨4, by decide, by simpa [exceptionalClasses] using hd⟩
    · exact ⟨3, by decide, by simpa [exceptionalClasses] using hz⟩
    · exact False.elim (hnw (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hdep, ht⟩, hng⟩))
  · refine ⟨0, by decide, ?_⟩
    change e ∈ AllAlignedPairs.nonaligned N L
    exact mem_sdiff.mpr ⟨heN, haligned⟩

theorem exceptional_activity_bound {Q N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hheight : Q ≤ (L + 1) ^ 3) (hlarge : 2 * (L + 1) ^ 4 < N) :
    CompatibleActivitySplit.absolute L (exceptional Q N H L) ≤
      ∑ i ∈ range 6, CompatibleActivitySplit.absolute L (exceptionalClasses Q N H L i) :=
  ActivityFamilyCover.finite_cover L _ _ _ (fun _ he hn ↦ exceptional_nonzero_cover hN hL hheight hlarge he hn)

theorem activity_decomposition (Q N H L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) =
      CompatibleActivitySplit.absolute L (good Q N H L) +
        CompatibleActivitySplit.absolute L (weak Q N H L) +
          CompatibleActivitySplit.absolute L (exceptional Q N H L) := by
  have hdis : Disjoint (good Q N H L ∪ weak Q N H L) (exceptional Q N H L) := by
    apply disjoint_left.mpr
    intro e he hex
    exact (mem_sdiff.mp hex).2 he
  unfold CompatibleActivitySplit.absolute
  rw [AbsoluteActivityDecomposition.absolute_eq_dependent (dyadicBlock N) L 2 hL (by decide),
    ← cover Q N H L, sum_union hdis, sum_union (disjoint_classes Q N H L).1]

end PaperP1.FiniteGoodChannelPartition
