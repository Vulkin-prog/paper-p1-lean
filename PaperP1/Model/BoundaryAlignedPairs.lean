module

public import PaperP1.Model.AlignedChannelFamilies
public import PaperP1.Model.ActivityFamilyCover
public import PaperP1.Combinatorics.ClosePairs

/-! # The height-one/two aligned pair populations and their finite boundary covers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundaryAlignedPairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedUnitCount PaperP1.EnlargedPairGeometry

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channel (N L a b : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 2).filter fun e ↦ ∃ x y : ℕ,
    e = {x, y} ∧ x < y ∧ Geometric a b x y L

def sources (N L a b : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦ xy.1 < xy.2 ∧ Geometric a b xy.1 xy.2 L

theorem data {N L a b : ℕ} {e : Finset ℕ} (he : e ∈ channel N L a b) :
    ∃ x y : ℕ, x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧ e = {x, y} ∧ x < y ∧ Geometric a b x y L := by
  obtain ⟨he, x, y, rfl, hxy, hg⟩ := mem_filter.mp he
  have heN := (mem_powersetCard.mp he).1
  exact ⟨x, y, heN (mem_insert_self x {y}), heN (mem_insert_of_mem (mem_singleton_self y)), rfl, hxy, hg⟩

theorem channel_eq_image (N L a b : ℕ) :
    channel N L a b = (sources N L a b).image fun xy ↦ {xy.1, xy.2} := by
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hx, hy, rfl, hxy, hg⟩ := data he
    exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hxy, hg⟩, rfl⟩
  · intro he
    obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
    obtain ⟨hN, hxy, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hN
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩,
      card_pair_eq_two_iff.mpr hxy.ne⟩, xy.1, xy.2, rfl, hxy, hg⟩

theorem height_two_sources_cover (N L : ℕ) :
    sources N L 1 2 ⊆ Icc N (N + 3 * (L + 1)) ×ˢ Icc (2 * N - 3 * (L + 1)) (2 * N) := by
  intro xy hxy
  obtain ⟨hN, _hxy, hg⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hN
  obtain ⟨hxlo, _hxhi⟩ := mem_Ico.mp hx
  obtain ⟨_hylo, hyhi⟩ := mem_Ico.mp hy
  have hgeomI : |(2 : ℤ) * xy.1 - xy.2| ≤ 3 * ((L + 1 : ℕ) : ℤ) := by
    simpa only [Geometric, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, one_mul] using hg
  have hh := (abs_le.mp hgeomI).2
  have heq : 2 * xy.1 ≤ xy.2 + 3 * (L + 1) := by omega
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨hxlo, by omega⟩, mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem height_two_card (N L : ℕ) :
    (channel N L 1 2).card ≤ 16 * (L + 1) ^ 2 := by
  have hxcard : (Icc N (N + 3 * (L + 1))).card = 3 * (L + 1) + 1 := by rw [Nat.card_Icc]; omega
  have hycard : (Icc (2 * N - 3 * (L + 1)) (2 * N)).card ≤ 3 * (L + 1) + 1 := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ (sources N L 1 2).card := by rw [channel_eq_image]; exact card_image_le
    _ ≤ (Icc N (N + 3 * (L + 1)) ×ˢ Icc (2 * N - 3 * (L + 1)) (2 * N)).card := card_le_card (height_two_sources_cover N L)
    _ ≤ (3 * (L + 1) + 1) ^ 2 := by rw [card_product, hxcard, pow_two]; exact Nat.mul_le_mul_left _ hycard
    _ ≤ (4 * (L + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by ring

theorem unit_one_empty {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hsep : x + L < y) :
    (units 1 1 x y L).card = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro h
  obtain ⟨u, hu⟩ := card_pos.mp h
  have heq := mem_units.mp hu
  simp only [one_mul] at heq
  rw [startCompleteVertexLabel_eq_offset hx, startCompleteVertexLabel_eq_offset hy] at heq
  have hu₁ := u.1.isLt
  have hu₂ := u.2.isLt
  omega

theorem height_one_cover {N L : ℕ} (hN : 2 ≤ N) :
    channel N L 1 1 ⊆ ClosePairs.pairs (dyadicBlock N) L ∪ AlignedChannelFamilies.zeroFamilies N L := by
  intro e he
  have heN := (mem_filter.mp he).1
  obtain ⟨x, y, hx, hy, rfl, hxy, hg⟩ := data he
  by_cases hnear : y ≤ x + L
  · exact mem_union_left _ (mem_filter.mpr ⟨heN, x, mem_insert_self _ _, y,
      mem_insert_of_mem (mem_singleton_self _), hxy, hnear⟩)
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨heN, x, y, 1, 1, rfl, hxy, by decide, by decide, by decide, ?_, hg, ?_⟩
    · simpa only [max_self] using (one_le_pow₀ (show 1 ≤ L + 1 by omega) : 1 ≤ (L + 1) ^ 3)
    · exact unit_one_empty (by have h := (mem_Ico.mp hx).1; omega)
        (by have h := (mem_Ico.mp hy).1; omega) (by omega)

end PaperP1.BoundaryAlignedPairs
