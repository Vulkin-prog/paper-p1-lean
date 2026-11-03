module

public import PaperP1.Arithmetic.CompressedPairIntersectionHosts
public import PaperP1.Asymptotics.DependentBlockPairsCount
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Two fixed-channel compressed pairs intersect at only N^(1+epsilon) actual hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPairIntersectionCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.CompressedPairIntersectionHosts

theorem fixed_offsets (a b c d : ℕ) (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j k l : Fin (L + 1),
      ((pairs N a b c d L i j k l).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NC, hc₀⟩ := DependentBlockPairsCount.article_10_3 (1 / 2) ((3 * (b + d) : ℕ) : ℝ)
    ((b + d : ℕ) : ℝ) C ε (by norm_num) (Nat.cast_nonneg _) hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NC NG), by omega, ?_⟩
  intro N hN L hband i j k l
  have hgeom := hg N (by omega) L hband
  have hNtwo : 2 ≤ N := by omega
  have hLN : L ≤ N := by omega
  have hb : 0 < b := ha.trans_le hab
  have hd : 0 < d := hc.trans_le hcd
  have hvalues : ∀ t : Fin 2, ∀ x ∈ range (3 * (b + d) * N + 1),
      ∀ v ∈ blocks N a b c d L i j k l t x,
      (1 / 2 : ℝ) * N ≤ v ∧ (v : ℝ) ≤ ((3 * (b + d) : ℕ) : ℝ) * N := by
    intro t x _hx v hv
    fin_cases t
    · have hv' : v ∈ CompressedSourceBlocks.block N a b L i j x := hv
      have h := CompressedChannelTargetHosts.block_heights hNtwo hLN ha hab i j hv'
      refine ⟨h.1, h.2.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast Nat.mul_le_mul_left 3 (Nat.le_add_right b d)
    · have hv' : v ∈ CompressedSourceBlocks.block N c d L k l x := hv
      have h := CompressedChannelTargetHosts.block_heights hNtwo hLN hc hcd k l hv'
      refine ⟨h.1, h.2.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      exact_mod_cast Nat.mul_le_mul_left 3 (Nat.le_add_left d b)
  have hdist : ∀ t : Fin 2, ∀ x ∈ range (3 * (b + d) * N + 1),
      ∀ v ∈ blocks N a b c d L i j k l t x,
      (((v : ℤ) - x).natAbs : ℝ) ≤ ((b + d : ℕ) : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    intro t x _hx v hv
    fin_cases t
    · have hv' : v ∈ CompressedSourceBlocks.block N a b L i j x := hv
      have h := CompressedChannelTargetHosts.block_distance (by omega : 0 < N) hab i j hv'
      exact_mod_cast h.trans (Nat.mul_le_mul_right (L + 1) (Nat.le_add_right b d))
    · have hv' : v ∈ CompressedSourceBlocks.block N c d L k l x := hv
      have h := CompressedChannelTargetHosts.block_distance (by omega : 0 < N) hcd k l hv'
      exact_mod_cast h.trans (Nat.mul_le_mul_right (L + 1) (Nat.le_add_left d b))
  calc
    _ ≤ ((DependentBlockPairs.pairs (range (3 * (b + d) * N + 1)) (blocks N a b c d L i j k l)).card : ℝ) := by
      exact_mod_cast finite_count hNtwo hLN ha hb hc hd i j k l
    _ ≤ _ := hc₀ N (by omega) L _ _ hband hvalues hdist

theorem uniform_count (a b c d : ℕ) (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((allPairs N a b c d L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨NC, _hNC, hc₀⟩ := fixed_offsets a b c d ha hab hc hcd C (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 4) 4 (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NS NP)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 4 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hB 4
      _ = CriticalBandScale.upperScale ^ 4 * (Real.log N) ^ 4 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_ofNat] using hp N (by omega)
  have hfinite := (card_le_card (all_pairs_cover N a b c d L)).trans card_biUnion_le
  calc
    _ ≤ ∑ w : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Fin (L + 1)),
        ((pairs N a b c d L w.1.1 w.1.2 w.2.1 w.2.2).card : ℝ) := by exact_mod_cast hfinite
    _ ≤ ∑ _w : (Fin (L + 1) × Fin (L + 1)) × (Fin (L + 1) × Fin (L + 1)),
        (N : ℝ) ^ (1 + ε / 2) := sum_le_sum fun w _ ↦ hc₀ N (by omega) L hband w.1.1 w.1.2 w.2.1 w.2.2
    _ = ((L + 1 : ℕ) : ℝ) ^ 4 * (N : ℝ) ^ (1 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.CompressedPairIntersectionCount
