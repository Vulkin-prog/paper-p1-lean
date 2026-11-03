module

public import PaperP1.Arithmetic.CompressedChannelTargetHosts
public import PaperP1.Asymptotics.DependentBlockPairsCount
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The actual fixed-channel pair/target population has unconditional count N^(1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedChannelTargetCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.CompressedChannelTargetHosts

theorem fixed_offsets (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      ((sourceTargets N a b L i j).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NC, hc⟩ := DependentBlockPairsCount.article_10_3 (1 / 2) ((3 * b : ℕ) : ℝ) (b : ℝ) C ε
    (by norm_num) (Nat.cast_nonneg _) hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NC NG), by omega, ?_⟩
  intro N hN L hband i j
  have hgeom := hg N (by omega) L hband
  have hNtwo : 2 ≤ N := by omega
  have hLN : L ≤ N := by omega
  have hb : 0 < b := ha.trans_le hab
  have hvalues : ∀ t : Fin 2, ∀ x ∈ range (3 * b * N + 1), ∀ v ∈ blocks N a b L i j t x,
      (1 / 2 : ℝ) * N ≤ v ∧ (v : ℝ) ≤ ((3 * b : ℕ) : ℝ) * N := by
    intro t x _hx v hv
    fin_cases t
    · exact CompressedChannelTargetHosts.block_heights hNtwo hLN ha hab i j hv
    · change v ∈ targetBlock N L x at hv
      by_cases hx : x ∈ dyadicBlock N
      · have hvraw : v ∈ NormalizedWindowSets.values x L := by simpa only [targetBlock, ite_eq_left hx] using hv
        have hraw := (OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp hx) hLN v hvraw).1
        have hcoef : (3 : ℝ) ≤ (3 * b : ℕ) := by exact_mod_cast Nat.mul_le_mul_left 3 (show 1 ≤ b by omega)
        exact ⟨hraw.1, hraw.2.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N))⟩
      · simp [targetBlock, hx] at hv
  have hdist : ∀ t : Fin 2, ∀ x ∈ range (3 * b * N + 1), ∀ v ∈ blocks N a b L i j t x,
      (((v : ℤ) - x).natAbs : ℝ) ≤ (b : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    intro t x _hx v hv
    fin_cases t
    · exact_mod_cast CompressedChannelTargetHosts.block_distance (by omega : 0 < N) hab i j hv
    · change v ∈ targetBlock N L x at hv
      by_cases hx : x ∈ dyadicBlock N
      · have hvraw : v ∈ NormalizedWindowSets.values x L := by simpa only [targetBlock, ite_eq_left hx] using hv
        have hraw : (((v : ℤ) - x).natAbs : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by
          exact_mod_cast (OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp hx) hLN v hvraw).2
        exact hraw.trans (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ b by exact_mod_cast hb) (Nat.cast_nonneg (L + 1)))
      · simp [targetBlock, hx] at hv
  calc
    _ ≤ ((DependentBlockPairs.pairs (range (3 * b * N + 1)) (blocks N a b L i j)).card : ℝ) := by
      exact_mod_cast source_targets_card hNtwo hLN ha hb i j
    _ ≤ _ := hc N (by omega) L (range (3 * b * N + 1)) (blocks N a b L i j) hband hvalues hdist

theorem uniform_count (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((allTargets N a b L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := fixed_offsets a b ha hab C (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 2) 2 (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NS NP)), by omega, ?_⟩
  intro N hN L hband
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hs N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2
      _ = CriticalBandScale.upperScale ^ 2 * (Real.log N) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_two] using hp N (by omega)
  have hfinite := (card_le_card (all_targets_cover N a b L)).trans (card_biUnion_le)
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), ((sourceTargets N a b L ij.1 ij.2).card : ℝ) := by
      exact_mod_cast hfinite
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (N : ℝ) ^ (1 + ε / 2) :=
      sum_le_sum fun ij _ ↦ hc N (by omega) L hband ij.1 ij.2
    _ = ((L + 1 : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (1 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, pow_two]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.CompressedChannelTargetCount
