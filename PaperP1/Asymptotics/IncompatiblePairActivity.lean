module

public import PaperP1.Model.IncompatiblePairActivity
public import PaperP1.Asymptotics.DependentProductMass

/-! # Unconditional N^(-1+epsilon) incompatible pair mass and signed/absolute gap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncompatiblePairActivityAsymptotic

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 2) ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := DependentProductMass.uniform_mass 2 C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NM NG), by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  exact (IncompatiblePairActivity.finite_bound G L hL).trans (hm N (by omega) L hband G hG)

theorem uniform_signed_absolute_gap (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard 2) -
        CompatibleActivitySplit.signed L (G.powersetCard 2) ∧
      CompatibleActivitySplit.absolute L (G.powersetCard 2) -
        CompatibleActivitySplit.signed L (G.powersetCard 2) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_activity C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NI (max NG NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  rw [IncompatiblePairActivity.signed_absolute_gap G L hL]
  constructor
  · exact mul_nonneg (by norm_num) (sum_nonneg fun I _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))
  · calc
      _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_left (hi N (by omega) L hband G hG) (by norm_num)
      _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring

end PaperP1.IncompatiblePairActivityAsymptotic
