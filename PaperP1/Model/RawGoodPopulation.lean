module

public import PaperP1.Model.GoodPrincipalPopulation

/-! # The original good-edge definition with only compatibility removed

The resulting raw population equals the two actual private channel
populations, including probability-zero pairs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawGoodPopulation

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic PaperP1.GoodEdgeCompression

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def RawGoodEdge (H : ℝ) (N L x y : ℕ) : Prop :=
  x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧ x < y ∧
    ¬Disjoint (squareClassSpace x L) (squareClassSpace y L) ∧
      ∃ a b : ℕ, Leading a b ∧ PrivateAbove H (NormalizedWindowSets.union a b x y L)

def edges (H : ℝ) (N L : ℕ) : Finset (Finset ℕ) :=
  (((dyadicBlock N) ×ˢ (dyadicBlock N)).filter (fun xy ↦ RawGoodEdge H N L xy.1 xy.2)).image
    (fun xy ↦ ({xy.1, xy.2} : Finset ℕ))

theorem good_iff_raw (H : ℝ) (N L x y : ℕ) :
    GoodEdge H N L x y ↔ RawGoodEdge H N L x y ∧ 0 < infiniteJointMoment L {x, y} := by
  unfold GoodEdge RawGoodEdge
  tauto

theorem edges_eq_channels {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    edges (H : ℝ) N L = PrivateChannelActivity.pairs N H 2 3 L ∪ PrivateChannelActivity.pairs N H 3 4 L := by
  ext e
  constructor
  · intro he
    obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
    obtain ⟨hx, hy, _horder, hdep, a, b, hlead, hprivate⟩ := (mem_filter.mp hxy).2
    obtain ⟨ha, hb, _hcop, _hle, _hb4⟩ := leading_properties hlead
    have htwo := CompressionRank.dependent_two_units ha hb (hN.trans (mem_Ico.mp hx).1)
      (hN.trans (mem_Ico.mp hy).1) hprivate.private hdep
    have hp : ({xy.1, xy.2} : Finset ℕ) ∈ PrivateChannelActivity.pairs N H a b L :=
      mem_image.mpr ⟨xy, PrivateChannelSources.mem_goodSources.mpr ⟨hx, hy, htwo, hprivate⟩, rfl⟩
    rcases hlead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact mem_union_left _ hp
    · exact mem_union_right _ hp
  · have hchannel (a b : ℕ) (hlead : Leading a b)
        (he : e ∈ PrivateChannelActivity.pairs N H a b L) : e ∈ edges (H : ℝ) N L := by
      obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
      obtain ⟨hx, hy, _htwo, hprivate⟩ := PrivateChannelSources.mem_goodSources.mp hxy
      have ha : 0 < a := (leading_properties hlead).1
      have hab : a < b := by rcases hlead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      have hlarge' : (a + b) * (L + 1) < N := by
        rcases hlead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      have horder := PrivateChannelSources.good_sources_order hN hab hlarge' hxy
      have hn := PrivateChannelRank.nullity_positive hN ha hab hlarge'
        (mem_image.mpr ⟨xy, hxy, rfl⟩)
      rw [runRelativeNullity, PaperP1.RetainedNullity.nullity_pair_eq_intersection _ _ _ horder.ne] at hn
      have hdep : ¬Disjoint (squareClassSpace xy.1 L) (squareClassSpace xy.2 L) := by
        intro hdis
        rw [disjoint_iff.mp hdis, finrank_bot] at hn
        omega
      exact mem_image.mpr ⟨xy, mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩,
        hx, hy, horder, hdep, a, b, hlead, hprivate⟩, rfl⟩
    intro he
    rcases mem_union.mp he with h23 | h34
    · exact hchannel 2 3 (Or.inl ⟨rfl, rfl⟩) h23
    · exact hchannel 3 4 (Or.inr ⟨rfl, rfl⟩) h34

end PaperP1.RawGoodPopulation
