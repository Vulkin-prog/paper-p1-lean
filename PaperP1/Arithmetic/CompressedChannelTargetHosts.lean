module

public import PaperP1.Arithmetic.CompressedSourceBlocks
public import PaperP1.Arithmetic.DependentBlockPairs
public import PaperP1.Model.IndependentTargetDeficit

/-! # Actual dependent targets after any fixed-channel source, over its compressed anchor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedChannelTargetHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount PaperP1.CompressedSourceBlocks
  PaperP1.DyadicEndpointPairs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def targetBlock (N L z : ℕ) : Finset ℕ := if z ∈ dyadicBlock N then values z L else ∅

def blocks (N a b L : ℕ) (i j : Fin (L + 1)) : Fin 2 → ℕ → Finset ℕ :=
  ![block N a b L i j, targetBlock N L]

def sourceTargets (N a b L : ℕ) (i j : Fin (L + 1)) : Finset ((ℕ × ℕ) × ℕ) :=
  ((sourcePairs N a b L i j) ×ˢ dyadicBlock N).filter fun p ↦
    IndependentTargetDeficit.targetDependent L {p.1.1, p.1.2} p.2

def allTargets (N a b L : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  (((dyadicBlock N) ×ˢ dyadicBlock N) ×ˢ dyadicBlock N).filter fun p ↦
    (units a b p.1.1 p.1.2 L).Nonempty ∧ IndependentTargetDeficit.targetDependent L {p.1.1, p.1.2} p.2

def hostKey (b L : ℕ) (i : Fin (L + 1)) (p : (ℕ × ℕ) × ℕ) : ℕ × ℕ :=
  (anchor b L i p.1, p.2)

theorem normalized_heights {N L x q b : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (hx : x ∈ dyadicBlock N) (hq : 0 < q) (hqb : q ≤ b)
    {n : ℕ} (hn : n ∈ normalized q x L) :
    (1 / 2 : ℝ) * N ≤ n ∧ (n : ℝ) ≤ (3 * b : ℕ) * (N : ℝ) := by
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
  have hraw := (OriginalWindowValueBounds.values_geometry N L x hN (mem_Ico.mp hx) hLN v hv).1
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqHi : (q : ℝ) ≤ b := by exact_mod_cast hqb
  have hlo := mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg (α := ℝ) v)
  have hhi := mul_le_mul hqHi hraw.2 (Nat.cast_nonneg v) (Nat.cast_nonneg b)
  push_cast
  exact ⟨hraw.1.trans (by simpa only [one_mul] using hlo), by nlinarith only [hhi]⟩

theorem block_distance {N a b L X : ℕ} (hN : 0 < N) (hab : a ≤ b)
    (i j : Fin (L + 1)) {n : ℕ} (hn : n ∈ block N a b L i j X) :
    ((n : ℤ) - X).natAbs ≤ b * (L + 1) := by
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hsource, hanchor⟩ := mem_filter.mp hxy
  have habs := source_abs_bound hN hab i j hsource hnu
  rw [hanchor, Int.abs_eq_natAbs] at habs
  have hnat : ((n : ℤ) - X).natAbs ≤ b * L := by exact_mod_cast habs
  exact hnat.trans (Nat.mul_le_mul_left b (Nat.le_succ L))

theorem block_heights {N a b L X : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (ha : 0 < a) (hab : a ≤ b) (i j : Fin (L + 1)) {n : ℕ}
    (hn : n ∈ block N a b L i j X) :
    (1 / 2 : ℝ) * N ≤ n ∧ (n : ℝ) ≤ (3 * b : ℕ) * (N : ℝ) := by
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hx, hy, _hu⟩ := mem_sourcePairs.mp (mem_filter.mp hxy).1
  rcases mem_union.mp hnu with hnX | hnY
  · exact normalized_heights hN hLN hx (ha.trans_le hab) le_rfl hnX
  · exact normalized_heights hN hLN hy ha hab hnY

theorem anchor_bound {N a b L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    anchor b L i xy < 3 * b * N + 1 := by
  have hx := (mem_sourcePairs.mp hxy).1
  have hvalue := (OriginalWindowValueBounds.values_geometry N L xy.1 hN (mem_Ico.mp hx) hLN
    (startCompleteVertexLabel xy.1 L i) (mem_values.mpr ⟨i, rfl⟩)).1.2
  have hnat : startCompleteVertexLabel xy.1 L i ≤ 3 * N := by exact_mod_cast hvalue
  have hmul := Nat.mul_le_mul_left b hnat
  unfold anchor
  nlinarith only [hmul]

theorem host_mem_pairs {N a b L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (ha : 0 < a) (hb : 0 < b) (i j : Fin (L + 1)) {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ sourceTargets N a b L i j) :
    hostKey b L i p ∈ DependentBlockPairs.pairs (range (3 * b * N + 1)) (blocks N a b L i j) := by
  obtain ⟨hpG, hdep⟩ := mem_filter.mp hp
  obtain ⟨hs, hz⟩ := mem_product.mp hpG
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_range.mpr (anchor_bound hN hLN i j hs), ?_⟩, ?_⟩
  · have hzhi := (mem_Ico.mp hz).2
    have hbn : N ≤ b * N := by simpa using Nat.mul_le_mul_right N (show 1 ≤ b by omega)
    exact mem_range.mpr (by dsimp [hostKey]; nlinarith only [hzhi, hbn])
  · apply (DependentBlockPairs.dependent_iff_intersection _ _).mpr
    change FiniteEvenSquareClasses.space (block N a b L i j (anchor b L i p.1)) ⊓
      FiniteEvenSquareClasses.space (targetBlock N L p.2) ≠ ⊥
    rw [space_eq hN ha hb i j hs, targetBlock, ite_eq_left hz, space_values, inf_comm]
    exact (IndependentTargetDeficit.target_pair L p.1.1 p.1.2 p.2).mp hdep

theorem host_key_injective {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) : Set.InjOn (hostKey b L i) (sourceTargets N a b L i j) := by
  intro p hp q hq heq
  have hpS := (mem_product.mp (mem_filter.mp hp).1).1
  have hqS := (mem_product.mp (mem_filter.mp hq).1).1
  have hfirst : anchor b L i p.1 = anchor b L i q.1 := congrArg Prod.fst heq
  have hsecond : p.2 = q.2 := congrArg (fun v : ℕ × ℕ ↦ v.2) heq
  exact Prod.ext (first_anchor_injective hN ha hb i j hpS hqS hfirst) hsecond

theorem source_targets_card {N a b L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (ha : 0 < a) (hb : 0 < b) (i j : Fin (L + 1)) :
    (sourceTargets N a b L i j).card ≤
      (DependentBlockPairs.pairs (range (3 * b * N + 1)) (blocks N a b L i j)).card :=
  card_le_card_of_injOn (hostKey b L i) (fun _ hp ↦ host_mem_pairs hN hLN ha hb i j hp)
    (host_key_injective (by omega) ha hb i j)

theorem all_targets_cover (N a b L : ℕ) :
    allTargets N a b L ⊆ univ.biUnion (fun ij : Fin (L + 1) × Fin (L + 1) ↦ sourceTargets N a b L ij.1 ij.2) := by
  intro p hp
  obtain ⟨hpG, hu, hdep⟩ := mem_filter.mp hp
  obtain ⟨hxy, hz⟩ := mem_product.mp hpG
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  obtain ⟨ij, hij⟩ := hu
  exact mem_biUnion.mpr ⟨ij, mem_univ _, mem_filter.mpr
    ⟨mem_product.mpr ⟨mem_sourcePairs.mpr ⟨hx, hy, mem_units.mp hij⟩, hz⟩, hdep⟩⟩

end PaperP1.CompressedChannelTargetHosts
