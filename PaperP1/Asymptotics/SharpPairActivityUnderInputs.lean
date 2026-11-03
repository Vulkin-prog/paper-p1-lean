module

public import PaperP1.Asymptotics.PairProfilesUnderGeometricInputs
public import PaperP1.Asymptotics.AlignedActivityPower

/-! # Sharp actual pair activity under the same explicit geometric inputs as the pair profile -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpPairActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousRunConversion
  PaperP1.PrincipalChannelEdges

theorem uniform_principal_profile (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 100)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
        |absoluteMass (dyadicBlock N) L - beta N H L| ≤ (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hp⟩ := PairProfilesUnderGeometricInputs.uniform_profiles C (ε / 2) D (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PairActivityCumulantGapAsymptotic.uniform_gap C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NP, _hNP, hp⟩ := hp hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
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

theorem uniform_pair_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 100)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        absoluteMass G L ≤ (N : ℝ) ^ (-2 / 3 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hp⟩ := uniform_principal_profile C (ε / 2) 8 (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := AlignedActivityPower.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := PrincipalChannelEdgesPhase.uniform_activity_gap C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := AlignedPrincipalActivity.uniform_geometry C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NP, _hNP, hp⟩ := hp hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NP (max NA (max NB (max NG NF)))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hprofile := (abs_le.mp (hp N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl)).2
  have hgap := (hb N (by omega) L (8 * (L + 1)) hband).2
  have hprincipal : CompatibleActivitySplit.absolute L (edges N (8 * (L + 1)) L) ≤
      CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) :=
    sum_le_sum_of_subset_of_nonneg
      (AllAlignedPairs.principal_subset (by omega)
        (hg N (by omega) L hband).2.1
        (hg N (by omega) L hband).2.2.2) (fun _ _ _ ↦ abs_nonneg _)
  have hsmall : (N : ℝ) ^ (-4 / 5 + ε / 2) ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have hsmaller : (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-2 / 3 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have haligned := ha N (by omega) L hband
  calc
    _ ≤ absoluteMass (dyadicBlock N) L := PairActivityHostCap.absoluteMass_mono hG L
    _ ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε / 2) := by
      linarith only [hprofile, hgap, hprincipal, haligned, hsmall, hsmaller]
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.SharpPairActivityUnderInputs
