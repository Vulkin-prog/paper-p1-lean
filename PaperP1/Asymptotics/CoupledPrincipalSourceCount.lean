module

public import PaperP1.Arithmetic.PrincipalSourcePatterns
public import PaperP1.Asymptotics.DependentBlockPairsCount
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Only N^(1+epsilon) principal source-pair codes have coupled effective spaces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoupledPrincipalSourceCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PrincipalSourcePatterns

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def coupled (N L : ℕ) (p q : Pattern L) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((sources N L p) ×ˢ (sources N L q)).filter fun xy ↦
    ¬Disjoint (squareClassSpace xy.1.1 L ⊔ squareClassSpace xy.1.2 L)
      (squareClassSpace xy.2.1 L ⊔ squareClassSpace xy.2.2 L)

def anchorPair {L : ℕ} (p q : Pattern L) (xy : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ × ℕ :=
  (anchor p xy.1, anchor q xy.2)

def blocks (N L : ℕ) (p q : Pattern L) : Fin 2 → ℕ → Finset ℕ := ![block N L p, block N L q]

theorem anchorPair_injective {N L : ℕ} (hN : 0 < N) (p q : Pattern L) :
    Set.InjOn (anchorPair p q)
      (((sources N L p ×ˢ sources N L q) : Finset ((ℕ × ℕ) × (ℕ × ℕ))) : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  intro xy hxy uv huv heq
  exact Prod.ext (anchor_injective hN p (mem_product.mp hxy).1 (mem_product.mp huv).1 (congrArg Prod.fst heq))
    (anchor_injective hN q (mem_product.mp hxy).2 (mem_product.mp huv).2 (congrArg Prod.snd heq))

theorem mem_dependent_pairs {N L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (p q : Pattern L)
    {xy : (ℕ × ℕ) × (ℕ × ℕ)} (hxy : xy ∈ coupled N L p q) :
    anchorPair p q xy ∈ DependentBlockPairs.pairs (range (12 * N + 1)) (blocks N L p q) := by
  obtain ⟨hsource, hdep⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hsource
  obtain ⟨ha, hb, _hab, _ha4, hb4, _hcop⟩ := properties p
  obtain ⟨hc, hd, _hcd, _hc4, hd4, _hcop'⟩ := properties q
  have hcommon : ∃ u : ℕ →₀ F₂, u ≠ 0 ∧ u ∈ (squareClassSpace xy.1.1 L ⊔ squareClassSpace xy.1.2 L) ∧
      u ∈ (squareClassSpace xy.2.1 L ⊔ squareClassSpace xy.2.2 L) := by
    by_contra hh
    apply hdep
    apply Submodule.disjoint_def.mpr
    intro u hu hv
    by_contra hne
    exact hh ⟨u, hne, hu, hv⟩
  obtain ⟨u, hne, hu, hv⟩ := hcommon
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, u, hne, ?_, ?_⟩
  · exact CompressedSourceBlocks.anchor_bound hN hLN hb4 p.2.1 p.2.2 hx
  · exact CompressedSourceBlocks.anchor_bound hN hLN hd4 q.2.1 q.2.2 hy
  · change u ∈ FiniteEvenSquareClasses.space (block N L p (anchor p xy.1))
    rwa [space_eq hN p hx]
  · change u ∈ FiniteEvenSquareClasses.space (block N L q (anchor q xy.2))
    rwa [space_eq hN q hy]

theorem uniform_count (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ p q : Pattern L,
      ((coupled N L p q).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NC, hc⟩ := DependentBlockPairsCount.article_10_3 (1 / 2) 12 4 C ε (by norm_num) (by norm_num) hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max 2 (max NC NG), by omega, ?_⟩
  intro N hN L hband p q
  have hN2 : 2 ≤ N := by omega
  have hLN : L ≤ N := by have hh := (hg N (by omega) L hband).2.2.2.1; omega
  have hsub : (coupled N L p q).card ≤
      (DependentBlockPairs.pairs (range (12 * N + 1)) (blocks N L p q)).card := by
    apply card_le_card_of_injOn (anchorPair p q)
    · exact fun _ hh ↦ mem_dependent_pairs hN2 hLN p q hh
    · intro xy hxy uv huv heq
      exact anchorPair_injective (by omega : 0 < N) p q (mem_filter.mp hxy).1 (mem_filter.mp huv).1 heq
  have hvalues : ∀ i, ∀ X ∈ range (12 * N + 1), ∀ n ∈ blocks N L p q i X,
      (1 / 2 : ℝ) * N ≤ n ∧ (n : ℝ) ≤ 12 * N := by
    intro i X _hX n hn
    fin_cases i
    · obtain ⟨ha, hb, _hab, ha4, hb4, _hcop⟩ := properties p
      exact CompressedSourceBlocks.block_heights hN2 hLN ha hb ha4 hb4 p.2.1 p.2.2 hn
    · obtain ⟨ha, hb, _hab, ha4, hb4, _hcop⟩ := properties q
      exact CompressedSourceBlocks.block_heights hN2 hLN ha hb ha4 hb4 q.2.1 q.2.2 hn
  have hdist : ∀ i, ∀ X ∈ range (12 * N + 1), ∀ n ∈ blocks N L p q i X,
      (((n : ℤ) - X).natAbs : ℝ) ≤ 4 * ((L + 1 : ℕ) : ℝ) := by
    intro i X _hX n hn
    fin_cases i
    · obtain ⟨_ha, _hb, hab, _ha4, hb4, _hcop⟩ := properties p
      exact_mod_cast CompressedSourceBlocks.block_distance (by omega : 0 < N) hab hb4 p.2.1 p.2.2 hn
    · obtain ⟨_ha, _hb, hab, _ha4, hb4, _hcop⟩ := properties q
      exact_mod_cast CompressedSourceBlocks.block_distance (by omega : 0 < N) hab hb4 q.2.1 q.2.2 hn
  exact (by exact_mod_cast hsub : ((coupled N L p q).card : ℝ) ≤
    (DependentBlockPairs.pairs (range (12 * N + 1)) (blocks N L p q)).card).trans
      (hc N (by omega) L (range (12 * N + 1)) (blocks N L p q) hband hvalues hdist)

end PaperP1.CoupledPrincipalSourceCount
