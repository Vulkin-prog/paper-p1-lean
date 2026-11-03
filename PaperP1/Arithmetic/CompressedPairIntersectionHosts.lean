module

public import PaperP1.Arithmetic.CompressedChannelTargetHosts

/-! # Literal pairs of compressed channel pairs with a nonzero common effective vector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPairIntersectionHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.CompressedSourceBlocks PaperP1.DyadicEndpointPairs PaperP1.NormalizedUnitCount

def blocks (N a b c d L : ℕ) (i j k l : Fin (L + 1)) : Fin 2 → ℕ → Finset ℕ :=
  ![block N a b L i j, block N c d L k l]

def pairs (N a b c d L : ℕ) (i j k l : Fin (L + 1)) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact ((sourcePairs N a b L i j) ×ˢ (sourcePairs N c d L k l)).filter fun p ↦
    (squareClassSpace p.1.1 L ⊔ squareClassSpace p.1.2 L) ⊓
      (squareClassSpace p.2.1 L ⊔ squareClassSpace p.2.2 L) ≠ ⊥

def hostKey (b d L : ℕ) (i k : Fin (L + 1)) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (anchor b L i p.1, anchor d L k p.2)

theorem host_mem_pairs {N a b c d L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (i j k l : Fin (L + 1)) {p : (ℕ × ℕ) × (ℕ × ℕ)}
    (hp : p ∈ pairs N a b c d L i j k l) :
    hostKey b d L i k p ∈ DependentBlockPairs.pairs (range (3 * (b + d) * N + 1))
      (blocks N a b c d L i j k l) := by
  classical
  obtain ⟨hpS, hdep⟩ := mem_filter.mp hp
  obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpS
  have hfirst := CompressedChannelTargetHosts.anchor_bound hN hLN i j hp₁
  have hsecond := CompressedChannelTargetHosts.anchor_bound hN hLN k l hp₂
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, ?_⟩
  · dsimp only [hostKey]
    nlinarith only [hfirst, Nat.zero_le (3 * d * N)]
  · dsimp only [hostKey]
    nlinarith only [hsecond, Nat.zero_le (3 * b * N)]
  · apply (DependentBlockPairs.dependent_iff_intersection _ _).mpr
    change FiniteEvenSquareClasses.space (block N a b L i j (anchor b L i p.1)) ⊓
      FiniteEvenSquareClasses.space (block N c d L k l (anchor d L k p.2)) ≠ ⊥
    rw [space_eq hN ha hb i j hp₁, space_eq hN hc hd k l hp₂]
    exact hdep

theorem host_key_injective {N a b c d L : ℕ} (hN : 0 < N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i j k l : Fin (L + 1)) :
    Set.InjOn (hostKey b d L i k) (pairs N a b c d L i j k l) := by
  intro p hp q hq heq
  obtain ⟨hp₁, hp₂⟩ := mem_product.mp (mem_filter.mp hp).1
  obtain ⟨hq₁, hq₂⟩ := mem_product.mp (mem_filter.mp hq).1
  exact Prod.ext
    (first_anchor_injective hN ha hb i j hp₁ hq₁ (congrArg Prod.fst heq))
    (first_anchor_injective hN hc hd k l hp₂ hq₂ (congrArg Prod.snd heq))

theorem finite_count {N a b c d L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (i j k l : Fin (L + 1)) :
    (pairs N a b c d L i j k l).card ≤
      (DependentBlockPairs.pairs (range (3 * (b + d) * N + 1)) (blocks N a b c d L i j k l)).card :=
  card_le_card_of_injOn (hostKey b d L i k)
    (fun _ hp ↦ host_mem_pairs hN hLN ha hb hc hd i j k l hp)
    (host_key_injective (by omega) ha hb hc hd i j k l)

def allPairs (N a b c d L : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact (((dyadicBlock N ×ˢ dyadicBlock N) ×ˢ (dyadicBlock N ×ˢ dyadicBlock N))).filter fun p ↦
    (units a b p.1.1 p.1.2 L).Nonempty ∧ (units c d p.2.1 p.2.2 L).Nonempty ∧
      (squareClassSpace p.1.1 L ⊔ squareClassSpace p.1.2 L) ⊓
        (squareClassSpace p.2.1 L ⊔ squareClassSpace p.2.2 L) ≠ ⊥

theorem all_pairs_cover (N a b c d L : ℕ) :
    allPairs N a b c d L ⊆ univ.biUnion
      (fun w : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Fin (L + 1)) ↦
        pairs N a b c d L w.1.1 w.1.2 w.2.1 w.2.2) := by
  classical
  intro p hp
  obtain ⟨hpG, hu₁, hu₂, hdep⟩ := mem_filter.mp hp
  obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpG
  obtain ⟨hx, hy⟩ := mem_product.mp hp₁
  obtain ⟨hz, hw⟩ := mem_product.mp hp₂
  obtain ⟨ij, hij⟩ := hu₁
  obtain ⟨kl, hkl⟩ := hu₂
  exact mem_biUnion.mpr ⟨(ij, kl), mem_univ _, mem_filter.mpr
    ⟨mem_product.mpr ⟨mem_sourcePairs.mpr ⟨hx, hy, mem_units.mp hij⟩,
      mem_sourcePairs.mpr ⟨hz, hw, mem_units.mp hkl⟩⟩, hdep⟩⟩

end PaperP1.CompressedPairIntersectionHosts
