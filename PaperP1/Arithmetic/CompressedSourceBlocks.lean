module

public import PaperP1.Arithmetic.DyadicEndpointPairs
public import PaperP1.Arithmetic.NormalizedPairGeometry
public import PaperP1.Arithmetic.OriginalWindowValueBounds
public import PaperP1.Arithmetic.CompressionRank

/-! # Exact source pairs at a fixed unit offset form uniformly bounded effective blocks over their anchors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedSourceBlocks

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.DyadicEndpointPairs
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

def anchor (b L : ℕ) (i : Fin (L + 1)) (xy : ℕ × ℕ) : ℕ := b * startCompleteVertexLabel xy.1 L i

def block (N a b L : ℕ) (i j : Fin (L + 1)) (X : ℕ) : Finset ℕ :=
  ((sourcePairs N a b L i j).filter fun xy ↦ anchor b L i xy = X).biUnion
    fun xy ↦ NormalizedWindowSets.union a b xy.1 xy.2 L

theorem block_eq {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    block N a b L i j (anchor b L i xy) = NormalizedWindowSets.union a b xy.1 xy.2 L := by
  ext n
  constructor
  · intro hn
    obtain ⟨uv, huv, hnu⟩ := mem_biUnion.mp hn
    obtain ⟨huvS, huvA⟩ := mem_filter.mp huv
    have heq : uv = xy := first_anchor_injective hN ha hb i j huvS hxy huvA
    simpa only [heq] using hnu
  · intro hn
    exact mem_biUnion.mpr ⟨xy, mem_filter.mpr ⟨hxy, rfl⟩, hn⟩

theorem source_abs_bound {N a b L : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j)
    {n : ℕ} (hn : n ∈ NormalizedWindowSets.union a b xy.1 xy.2 L) :
    |(n : ℤ) - (anchor b L i xy : ℕ)| ≤ ((b * L : ℕ) : ℤ) := by
  obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
  have hcast : (n : ℤ) ∈ (NormalizedWindowSets.union a b xy.1 xy.2 L).image (fun m : ℕ ↦ (m : ℤ)) :=
    mem_image.mpr ⟨n, hn, rfl⟩
  rw [NormalizedMotifs.translated_motif (hN.trans_le (mem_Ico.mp hx).1)
    (hN.trans_le (mem_Ico.mp hy).1) i j hunit] at hcast
  obtain ⟨w, hw, heq⟩ := mem_image.mp hcast
  have hdiff : (n : ℤ) - (anchor b L i xy : ℕ) = w := by
    change (n : ℤ) - ((b * startCompleteVertexLabel xy.1 L i : ℕ) : ℤ) = w
    push_cast at heq ⊢
    linarith only [heq]
  rw [hdiff]
  exact_mod_cast NormalizedMotifs.motif_bound hab i j w hw

theorem block_distance {N a b L X : ℕ} (hN : 0 < N) (hab : a ≤ b) (hb4 : b ≤ 4)
    (i j : Fin (L + 1)) {n : ℕ} (hn : n ∈ block N a b L i j X) :
    ((n : ℤ) - X).natAbs ≤ 4 * (L + 1) := by
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hsource, hanchor⟩ := mem_filter.mp hxy
  have habs := source_abs_bound hN hab i j hsource hnu
  rw [hanchor, Int.abs_eq_natAbs] at habs
  have hnat : ((n : ℤ) - X).natAbs ≤ b * L := by exact_mod_cast habs
  exact hnat.trans (Nat.mul_le_mul hb4 (Nat.le_succ L))

theorem normalized_heights {N L x q : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (hx : x ∈ dyadicBlock N) (hq : 0 < q) (hq4 : q ≤ 4)
    {n : ℕ} (hn : n ∈ normalized q x L) : (1 / 2 : ℝ) * N ≤ n ∧ (n : ℝ) ≤ 12 * N := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
  have hraw := (OriginalWindowValueBounds.values_geometry N L x hN (mem_Ico.mp hx) hLN v hv).1
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqHi : (q : ℝ) ≤ 4 := by exact_mod_cast hq4
  have hlo := mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg (α := ℝ) v)
  have hhi := mul_le_mul hqHi hraw.2 (Nat.cast_nonneg v) (by norm_num : (0 : ℝ) ≤ 4)
  push_cast
  exact ⟨hraw.1.trans (by simpa only [one_mul] using hlo), by nlinarith only [hhi]⟩

theorem block_heights {N a b L X : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (ha : 0 < a) (hb : 0 < b) (ha4 : a ≤ 4) (hb4 : b ≤ 4)
    (i j : Fin (L + 1)) {n : ℕ} (hn : n ∈ block N a b L i j X) :
    (1 / 2 : ℝ) * N ≤ n ∧ (n : ℝ) ≤ 12 * N := by
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hx, hy, _hunit⟩ := mem_sourcePairs.mp (mem_filter.mp hxy).1
  rcases mem_union.mp hnu with hnX | hnY
  · exact normalized_heights hN hLN hx hb hb4 hnX
  · exact normalized_heights hN hLN hy ha ha4 hnY

theorem anchor_bound {N a b L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hb4 : b ≤ 4)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    anchor b L i xy < 12 * N + 1 := by
  have hx := (mem_sourcePairs.mp hxy).1
  have hvalue := (OriginalWindowValueBounds.values_geometry N L xy.1 hN (mem_Ico.mp hx) hLN
    (startCompleteVertexLabel xy.1 L i) (mem_values.mpr ⟨i, rfl⟩)).1.2
  have hnat : startCompleteVertexLabel xy.1 L i ≤ 3 * N := by exact_mod_cast hvalue
  have hmul := Nat.mul_le_mul hb4 hnat
  unfold anchor
  nlinarith only [hmul]

theorem space_eq {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    FiniteEvenSquareClasses.space (block N a b L i j (anchor b L i xy)) =
      squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
  rw [block_eq (by omega : 0 < N) ha hb i j hxy]
  obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
  exact space_union ha hb (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1)
    (CompressionRank.units_intersection_nonempty ⟨(i, j), mem_units.mpr hunit⟩)

end PaperP1.CompressedSourceBlocks
