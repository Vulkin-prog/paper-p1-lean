module

public import PaperP1.Asymptotics.PairProfiles
public import PaperP1.Asymptotics.AlignedActivityPower

/-! # The actual principal pair-activity profile without unproved inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpPairActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousRunConversion
  PaperP1.PrincipalChannelEdges

theorem uniform_principal_profile (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        |absoluteMass (dyadicBlock N) L - beta N H L| ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := PairProfiles.uniform_profiles C (ε / 2) D (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PairActivityCumulantGapAsymptotic.uniform_gap C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NP (max NG NF)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hprofile := abs_le.mp (hp N (by omega) L H hband hcut hH).1
  have hgap := hg N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hpow : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have hR : 0 ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hfinite : |absoluteMass (dyadicBlock N) L - beta N H L| ≤
      2 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
    change 0 ≤ absoluteMass (dyadicBlock N) L - _ ∧ absoluteMass (dyadicBlock N) L - _ ≤ _ at hgap
    exact abs_le.mpr ⟨by linarith only [hprofile.1, hgap.1, hR],
      by linarith only [hprofile.2, hgap.2, hpow, hR]⟩
  exact hfinite.trans (by
    convert hf N (by omega) using 1
    congr 1
    ring)

end PaperP1.SharpPairActivity
