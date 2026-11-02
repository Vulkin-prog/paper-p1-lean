module

public import PaperP1.Asymptotics.DenseNonalignedProfileReduction
public import PaperP1.Asymptotics.PrivateChannelMassRate
public import PaperP1.Asymptotics.ChannelMainTermBounds

/-! # Explicit two-channel profile with the literal dense nonaligned remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoChannelDenseProfileReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges
  PaperP1.PrivateChannelSources PaperP1.ChannelMainTermBounds

theorem uniform_bound (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
        (mainTerm N L 2 3 + mainTerm N L 3 4)| ≤
          2 * CompatibleActivitySplit.absolute L (DenseNonalignedProfileReduction.dense N L) +
            (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := DenseNonalignedProfileReduction.uniform_bound C (ε / 2) D (by positivity)
  obtain ⟨NM23, hm23⟩ := PrivateChannelMassRate.mass_error_rpow C D 2 3
    (by decide) (by decide) (by decide) (by decide) (ε / 2) (by positivity)
  obtain ⟨NM34, hm34⟩ := PrivateChannelMassRate.mass_error_rpow C D 3 4
    (by decide) (by decide) (by decide) (by decide) (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := AlignedPrincipalActivity.uniform_geometry C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NR (max NM23 (max NM34 (max NG NF)))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have h23 := hm23 N (by omega) L H hband (by omega) hH
  have h34 := hm34 N (by omega) L H hband (by omega) hH
  change |channelMass N H 2 3 L - mainTerm N L 2 3| ≤ (N : ℝ) ^ (-1 + ε / 2) at h23
  change |channelMass N H 3 4 L - mainTerm N L 3 4| ≤ (N : ℝ) ^ (-1 + ε / 2) at h34
  have hbeta := beta_eq (H := H) (by omega : 2 ≤ N) (hg N (by omega) L hband).2.2.2
  have hsplit : 2 * beta N H L - (mainTerm N L 2 3 + mainTerm N L 3 4) =
      (channelMass N H 2 3 L - mainTerm N L 2 3) +
        (channelMass N H 3 4 L - mainTerm N L 3 4) := by
    rw [hbeta]
    ring
  have hmass : |2 * beta N H L - (mainTerm N L 2 3 + mainTerm N L 3 4)| ≤
      2 * (N : ℝ) ^ (-1 + ε / 2) := by
    rw [hsplit]
    have ht := abs_add_le (channelMass N H 2 3 L - mainTerm N L 2 3)
      (channelMass N H 3 4 L - mainTerm N L 3 4)
    linarith only [ht, h23, h34]
  have hsmall : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-4 / 5 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have hprofile := hr N (by omega) L H hband hcut hH
  calc
    _ ≤ |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 2 * beta N H L| +
        |2 * beta N H L - (mainTerm N L 2 3 + mainTerm N L 3 4)| := by
      simpa only [Real.dist_eq] using dist_triangle
        (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)
        (2 * beta N H L) (mainTerm N L 2 3 + mainTerm N L 3 4)
    _ ≤ 2 * CompatibleActivitySplit.absolute L (DenseNonalignedProfileReduction.dense N L) +
        3 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
      linarith only [hprofile, hmass, hsmall]
    _ ≤ 2 * CompatibleActivitySplit.absolute L (DenseNonalignedProfileReduction.dense N L) +
        (N : ℝ) ^ ((-4 / 5 + ε / 2) + ε / 2) := by
      have hh := hf N (by omega)
      linarith only [hh]
    _ = _ := by congr 2; ring

end PaperP1.TwoChannelDenseProfileReduction
