module

public import PaperP1.Model.PrincipalAlignedCover
public import PaperP1.Asymptotics.BoundaryAlignedActivity
public import PaperP1.Asymptotics.LogHeightAlignedActivity
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase

/-! # The whole literal aligned pair activity equals principal beta up to N^(-4/5+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedPrincipalActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges
  PaperP1.PrivateChannelSources

theorem uniform_geometry (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < L ∧ 4 ≤ (L + 1) ^ 3 ∧ 2 * (L + 1) ^ 4 < N ∧ 29 * (L + 1) < N := by
  obtain ⟨NP, _hNP, hp⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 4
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 2 (by norm_num) 4
  refine ⟨max 2 (max NP (max NG NL)), by omega, ?_⟩
  intro N hN L hband
  have hB := (hg N (by omega) L hband).2.1
  have hheight : 4 ≤ (L + 1) ^ 3 := hB.trans (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  exact ⟨(hp N (by omega) L hband).1, hheight,
    by exact_mod_cast hl N (by omega) L hband, (hp N (by omega) L hband).2⟩

set_option maxHeartbeats 1000000 in
theorem uniform_absolute (C ε : ℝ) (D : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      |CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) - beta N H L| ≤
        (N : ℝ) ^ (-4 / 5 + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N1, _hN1, h1⟩ := BoundaryAlignedActivity.height_one C δ hδ
  obtain ⟨N2, _hN2, h2⟩ := BoundaryAlignedActivity.height_two C δ hδ
  obtain ⟨N23, _hN23, h23⟩ := PrivateChannelActivityRate.uniform_absolute_comparison C δ 2 3 (by decide) (by decide) hδ
  obtain ⟨N34, _hN34, h34⟩ := PrivateChannelActivityRate.uniform_absolute_comparison C δ 3 4 (by decide) (by decide) hδ
  obtain ⟨NB23, _hNB23, hb23⟩ := NormalizedDefectPairActivity.uniform_activity C δ D 2 3 (by decide) (by decide) (by decide) hδ
  obtain ⟨NB34, _hNB34, hb34⟩ := NormalizedDefectPairActivity.uniform_activity C δ D 3 4 (by decide) (by decide) (by decide) hδ
  obtain ⟨NZ, _hNZ, hz⟩ := ZeroUnitAlignedActivity.uniform_bound C δ hδ
  obtain ⟨NT, _hNT, ht⟩ := LogHeightAlignedActivity.source_tail_from_five C δ hδ
  obtain ⟨NP, _hNP, hp⟩ := PrincipalChannelEdgesPhase.uniform_activity_gap C δ hδ
  obtain ⟨NG, _hNG, hg⟩ := uniform_geometry C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 8 (-4 / 5 + δ) δ hδ
  refine ⟨max 2 (max N1 (max N2 (max N23 (max N34 (max NB23 (max NB34 (max NZ (max NT (max NP (max NG (NF))))))))))), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hL, hheight, hlarge, h29⟩ := hg N (by omega) L hband
  let S := (N : ℝ) ^ (-1 + δ)
  let T := (N : ℝ) ^ (-4 / 5 + δ)
  have hST : S ≤ T := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith)
  have hbound := PrincipalAlignedCover.finite_bound (H := H) (by omega) hL hheight hlarge
  have hb23small : CompatibleActivitySplit.absolute L (NormalizedDefectPairActivity.pairs N H 2 3 L) ≤ S :=
    (hb23 N (by omega) L H hband (by omega) hH).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith))
  have hb34small : CompatibleActivitySplit.absolute L (NormalizedDefectPairActivity.pairs N H 3 4 L) ≤ S :=
    (hb34 N (by omega) L H hband (by omega) hH).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith))
  have hupper : CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) - beta N H L ≤ 8 * T := by
    rw [PrincipalChannelEdges.beta_eq (by omega) h29]
    have hr23 := (abs_le.mp (h23 N (by omega) L H hband)).2
    have hr34 := (abs_le.mp (h34 N (by omega) L H hband)).2
    have hb1 := h1 N (by omega) L hband
    have hb2 := (h2 N (by omega) L hband).2
    have hbZ := hz N (by omega) L hband
    have hbT := ht N (by omega) L hband
    dsimp only [S, T] at hb23small hb34small hST ⊢
    linarith only [hbound, hr23, hr34, hb1, hb2, hb23small, hb34small, hbZ, hbT, hST]
  have hprincipal : CompatibleActivitySplit.absolute L (PrincipalChannelEdges.edges N H L) ≤
      CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) :=
    sum_le_sum_of_subset_of_nonneg (AllAlignedPairs.principal_subset (by omega) hheight h29) (fun _ _ _ ↦ abs_nonneg _)
  have hgap := (hp N (by omega) L H hband).2
  have hsmall : S ≤ (N : ℝ) ^ (-4 / 5 + ε) := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε])
  have hupperFinal : 8 * T ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    dsimp [δ]
    ring
  exact abs_le.mpr ⟨by dsimp only [S] at hsmall; linarith only [hprincipal, hgap, hsmall], hupper.trans hupperFinal⟩

end PaperP1.AlignedPrincipalActivity
