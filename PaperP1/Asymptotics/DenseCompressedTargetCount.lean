module

public import PaperP1.Asymptotics.BoundedWidthDenseCount
public import PaperP1.Arithmetic.CompressedTargetCenters

/-! # Article Lemma15.3 for actual compressed centers in every fixed channel, with all unit-offset patterns included -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseCompressedTargetCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.CriticalBandScale
  PaperP1.CompressedTargetCenters PaperP1.CompressedSourceBlocks

local instance denseCompressedPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem uniform_offsets (s a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ i j : Fin (L + 1), ∀ x : Fin s → ℕ, (∀ q, x q ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ q, squareClassSpace (x q) L →
        ((denseCenters N a b L i j W η).card : ℝ) ≤ (N : ℝ) ^ ε := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨Nc, _hNc, hc⟩ := BoundedWidthDenseCount.uniform_count s b (by omega)
    (1 / 2) (3 * (b : ℝ)) C η ε (by norm_num) hη hε
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max 3 (max Nc Ng), by omega, ?_⟩
  intro N hN L hband i j x hx W hW
  have hgeom := hg N (by omega) L hband
  have hLN : L ≤ N := by have h := hgeom.2.2.2.1; omega
  apply hc N (by omega) L hband x hx W hW (block N a b L i j) (denseCenters N a b L i j W η)
  intro X hX
  obtain ⟨hcenter, hdense⟩ := (mem_dense_centers N a b L i j W η X).mp hX
  have hbnds := center_bounds (by omega) hLN hb i j hcenter
  exact ⟨hbnds.1, hbnds.2, fun n hn ↦ block_width (by omega) hab i j hn, hdense⟩

theorem article_15_3 (s a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ q, x q ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ q, squareClassSpace (x q) L →
        ((allDenseCenters N a b L W η).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nc, _hNc, hc⟩ := uniform_offsets s a b ha hab C η (ε / 2) hη (by positivity)
  obtain ⟨Np, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 2 (ε / 2) (by positivity)
  obtain ⟨Ng, hg⟩ := critical_band_scale C
  refine ⟨max 3 (max Nc (max Np Ng)), by omega, ?_⟩
  intro N hN L hband x hx W hW
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly : (L + 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L + 1 : ℝ) ^ 2)] using
      hp N (by omega) L (hg N (by omega) L hband).2
  have hfinite : ((allDenseCenters N a b L W η).card : ℝ) ≤
      ∑ ij : Fin (L + 1) × Fin (L + 1), ((denseCenters N a b L ij.1 ij.2 W η).card : ℝ) := by
    exact_mod_cast (card_biUnion_le : (allDenseCenters N a b L W η).card ≤ _)
  calc
    _ ≤ _ := hfinite
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (N : ℝ) ^ (ε / 2) :=
      sum_le_sum (fun ij _ ↦ hc N (by omega) L hband ij.1 ij.2 x hx W hW)
    _ = (L + 1 : ℝ) ^ 2 * (N : ℝ) ^ (ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, pow_two]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hNr.le _)
    _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring

end PaperP1.DenseCompressedTargetCount
