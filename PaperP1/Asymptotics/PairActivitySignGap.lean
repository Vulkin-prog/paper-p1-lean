module

public import PaperP1.Model.ActivitySignGap
public import PaperP1.Asymptotics.IncompatiblePairActivity

/-! # Every original dyadic pair subfamily has sign gap at most N^(-1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairActivitySignGap

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ), F ⊆ (dyadicBlock N).powersetCard 2 →
      0 ≤ CompatibleActivitySplit.absolute L F - CompatibleActivitySplit.signed L F ∧
        CompatibleActivitySplit.absolute L F - CompatibleActivitySplit.signed L F ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := IncompatiblePairActivityAsymptotic.uniform_activity C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NI (max NG NF)), by omega, ?_⟩
  intro N hN L hband F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  refine ⟨ActivitySignGap.nonneg L F, ?_⟩
  calc
    _ ≤ CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) -
        CompatibleActivitySplit.signed L ((dyadicBlock N).powersetCard 2) := ActivitySignGap.mono L hF
    _ = 2 * CompatibleActivitySplit.incompatibleAbsolute L ((dyadicBlock N).powersetCard 2) :=
      IncompatiblePairActivity.signed_absolute_gap (dyadicBlock N) L hL
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_left
      (hi N (by omega) L hband (dyadicBlock N) (subset_refl _)) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PairActivitySignGap
