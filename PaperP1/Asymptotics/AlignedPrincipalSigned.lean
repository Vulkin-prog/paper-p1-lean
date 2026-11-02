module

public import PaperP1.Asymptotics.AlignedPrincipalActivity
public import PaperP1.Asymptotics.PairActivitySignGap

/-! # The complete aligned signed pair sum has the actual principal beta profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedPrincipalSigned

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges

theorem uniform_bound (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - beta N H L| ≤
        (N : ℝ) ^ (-4 / 5 + ε) := by
  classical
  obtain ⟨NA, _hNA, ha⟩ := AlignedPrincipalActivity.uniform_absolute C (ε / 2) D (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := PairActivitySignGap.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NA (max NS NF)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgap := hs N (by omega) L hband (AllAlignedPairs.families N L) (filter_subset _ _)
  have hsmall : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have hmain := abs_le.mp (ha N (by omega) L H hband hcut hH)
  have hfinite : |CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - beta N H L| ≤
      2 * (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    abs_le.mpr ⟨by linarith only [hgap.2, hsmall, hmain.1], by linarith only [hgap.1, hmain.1, hmain.2]⟩
  calc
    _ ≤ _ := hfinite
    _ ≤ (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.AlignedPrincipalSigned
