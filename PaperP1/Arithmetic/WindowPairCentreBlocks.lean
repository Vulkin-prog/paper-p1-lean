module

public import PaperP1.Arithmetic.CompressedSourceBlocks
public import PaperP1.Arithmetic.FixedChannelSourceGeometry
public import PaperP1.Arithmetic.ExpandedAsymmetricSupportEnvelope

/-! # Exact unit pairs compressed about scaled original starts

The centre `b*x` lies in a literal dyadic block of scale `b*N`.
All actual normalized values remain within a fixed logarithmic width.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowPairCentreBlocks

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.DyadicEndpointPairs PaperP1.NormalizedWindowSets

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def centre (b : ℕ) (xy : ℕ × ℕ) : ℕ := b * xy.1

def block (N a b L : ℕ) (i j : Fin (L + 1)) (X : ℕ) : Finset ℕ :=
  ((sourcePairs N a b L i j).filter fun xy ↦ centre b xy = X).biUnion
    fun xy ↦ NormalizedWindowSets.union a b xy.1 xy.2 L

theorem centre_injective {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) : Set.InjOn (centre b) (sourcePairs N a b L i j) := by
  intro xy hxy uv huv heq
  apply FixedChannelSourceGeometry.first_projection_injective hN ha i j hxy huv
  exact Nat.eq_of_mul_eq_mul_left hb heq

theorem block_eq {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    block N a b L i j (centre b xy) = NormalizedWindowSets.union a b xy.1 xy.2 L := by
  ext n
  constructor
  · intro hn
    obtain ⟨uv, huv, hnu⟩ := mem_biUnion.mp hn
    obtain ⟨huvS, huvC⟩ := mem_filter.mp huv
    have heq := centre_injective hN ha hb i j huvS hxy huvC
    simpa only [heq] using hnu
  · intro hn
    exact mem_biUnion.mpr ⟨xy, mem_filter.mpr ⟨hxy, rfl⟩, hn⟩

theorem space_eq {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    FiniteEvenSquareClasses.space (block N a b L i j (centre b xy)) =
      squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
  rw [block_eq (by omega : 0 < N) ha hb i j hxy]
  obtain ⟨hx, hy, hu⟩ := mem_sourcePairs.mp hxy
  exact NormalizedWindowSets.space_union ha hb (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1)
    (CompressionRank.units_intersection_nonempty ⟨(i, j), NormalizedUnitCount.mem_units.mpr hu⟩)

theorem anchor_distance {N b L : ℕ} (hN : 0 < N) (i : Fin (L + 1)) {xy : ℕ × ℕ}
    (hx : xy.1 ∈ dyadicBlock N) :
    |(CompressedSourceBlocks.anchor b L i xy : ℤ) - (centre b xy : ℕ)| ≤ ((b * (L + 1) : ℕ) : ℤ) := by
  have hxpos : 0 < xy.1 := hN.trans_le (mem_Ico.mp hx).1
  have hcoord : |(startCompleteVertexLabel xy.1 L i : ℤ) - xy.1| ≤ ((L + 1 : ℕ) : ℤ) := by
    rw [startCompleteVertexLabel_eq_offset hxpos]
    have hi := i.isLt
    apply abs_le.mpr
    constructor <;> omega
  change |((b * startCompleteVertexLabel xy.1 L i : ℕ) : ℤ) - ((b * xy.1 : ℕ) : ℤ)| ≤ _
  push_cast
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b)]
  exact mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg b)

theorem value_distance {N a b L : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j)
    {n : ℕ} (hn : n ∈ NormalizedWindowSets.union a b xy.1 xy.2 L) :
    |(n : ℤ) - (centre b xy : ℕ)| ≤ ((2 * b * (L + 1) : ℕ) : ℤ) := by
  have hsource := CompressedSourceBlocks.source_abs_bound hN hab i j hxy hn
  have hanchor := anchor_distance hN (b := b) i (mem_sourcePairs.mp hxy).1
  have htriangle := abs_sub_le (n : ℤ) (CompressedSourceBlocks.anchor b L i xy : ℤ) (centre b xy : ℕ)
  push_cast at hsource hanchor ⊢
  nlinarith only [hsource, hanchor, htriangle, Nat.cast_nonneg (α := ℤ) b]

theorem block_distance {N a b L X : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (i j : Fin (L + 1)) {n : ℕ} (hn : n ∈ block N a b L i j X) :
    |(n : ℤ) - X| ≤ ((2 * b * (L + 1) : ℕ) : ℤ) := by
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hsource, hcentre⟩ := mem_filter.mp hxy
  simpa only [hcentre] using value_distance hN hab i j hsource hnu

theorem block_card {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) (X : ℕ) : (block N a b L i j X).card ≤ 2 * (L + 1) := by
  by_cases he : (block N a b L i j X).Nonempty
  · obtain ⟨n, hn⟩ := he
    obtain ⟨xy, hxy, _hnu⟩ := mem_biUnion.mp hn
    obtain ⟨hsource, hcentre⟩ := mem_filter.mp hxy
    rw [← hcentre, block_eq hN ha hb i j hsource]
    have hxpos := hN.trans_le (mem_Ico.mp (mem_sourcePairs.mp hsource).1).1
    have hypos := hN.trans_le (mem_Ico.mp (mem_sourcePairs.mp hsource).2.1).1
    exact (card_union_le _ _).trans_eq (by rw [card_normalized hb hxpos, card_normalized ha hypos]; omega)
  · rw [not_nonempty_iff_eq_empty.mp he]
    simp

theorem scaled_dyadic {N b x : ℕ} (hb : 0 < b) (hx : x ∈ dyadicBlock N) :
    b * x ∈ dyadicBlock (b * N) := by
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hx
  exact mem_Ico.mpr ⟨Nat.mul_le_mul_left b hlo, by nlinarith only [Nat.mul_lt_mul_of_pos_left hhi hb]⟩

theorem expanded_centre {N b d x : ℕ} (hd : 0 < d) (hdb : d ≤ b) (hx : x ∈ dyadicBlock N) :
    b * x ∈ ExpandedAsymmetricSupportEnvelope.block (d * N) (2 * b) := by
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hx
  have hb : 0 < b := hd.trans_le hdb
  have hbase : d * N ≤ b * x := (Nat.mul_le_mul_right N hdb).trans (Nat.mul_le_mul_left b hlo)
  have htop : b * x < 2 * b * N := by nlinarith only [Nat.mul_lt_mul_of_pos_left hhi hb]
  have hscale : N ≤ d * N := by simpa only [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ d by omega)
  have hupper : 2 * b * N ≤ 2 * b * (d * N) := Nat.mul_le_mul_left (2 * b) hscale
  exact mem_Ico.mpr ⟨hbase, by nlinarith only [htop, hupper, Nat.zero_le (d * N)]⟩

end PaperP1.WindowPairCentreBlocks
