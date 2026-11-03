module

public import PaperP1.Arithmetic.DenseCompressedPairs
public import PaperP1.Asymptotics.DenseCompressedTargetCount

/-! # All actual fixed-channel dense target pairs have subpower count without private normalizations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseCompressedPairCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.CriticalBandScale

theorem uniform_count (s a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (C η ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ q, x q ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ q, squareClassSpace (x q) L →
        ((DenseCompressedPairs.pairs N a b L W η).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NC, _hNC, hc⟩ := DenseCompressedTargetCount.uniform_offsets s a b ha hab C η (ε / 2) hη (by positivity)
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 2 (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := critical_band_scale C
  refine ⟨3 + NC + NP + NG, by omega, ?_⟩
  intro N hN L hband x hx W hW
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly : (L + 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L + 1 : ℝ) ^ 2)] using
      hp N (by omega) L (hg N (by omega) L hband).2
  have hfinite : ((DenseCompressedPairs.pairs N a b L W η).card : ℝ) ≤
      ∑ ij : Fin (L + 1) × Fin (L + 1), ((CompressedTargetCenters.denseCenters N a b L ij.1 ij.2 W η).card : ℝ) := by
    exact_mod_cast DenseCompressedPairs.finite_card_bound (by omega : 2 ≤ N) ha (ha.trans_le hab) W η
  calc
    _ ≤ _ := hfinite
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (N : ℝ) ^ (ε / 2) :=
      sum_le_sum fun ij _ ↦ hc N (by omega) L hband ij.1 ij.2 x hx W hW
    _ = (L + 1 : ℝ) ^ 2 * (N : ℝ) ^ (ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, pow_two]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.DenseCompressedPairCount
