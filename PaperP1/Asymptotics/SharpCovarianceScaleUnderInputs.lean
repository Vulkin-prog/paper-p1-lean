module

public import PaperP1.Asymptotics.SecondFactorialCorrectionLower
public import PaperP1.Asymptotics.SharpPairActivityUnderInputs
public import PaperP1.Asymptotics.FinitePairDeficitInputs

/-! # The actual regular covariance is bounded by the literal nominal second factorial correction under the recorded geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpCovarianceScaleUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousRunConversion
  PaperP1.SecondFactorialCorrection PaperP1.FinitePairDeficitInputs

theorem uniform_absolute_scale (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        absoluteMass G L ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
  obtain ⟨D, j, j₁, j₂, hD, hp⟩ := SharpPairActivityUnderInputs.uniform_principal_profile C (1 / 15) 8 (by norm_num)
  obtain ⟨_c, K, _hc, hK, NB, _hNB, hb⟩ := PrincipalChannelEdgesPhase.positive_phase C 8
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨⟨D, j, j₁, j₂, hD⟩, ?_⟩
  intro hgeo
  obtain ⟨NP, _hNP, hh⟩ := hp hgeo.source hgeo.ordinaryTwo hgeo.ordinaryThree
    hgeo.sourceCurves hgeo.ordinaryTwoCurves hgeo.ordinaryThreeCurves
  refine ⟨K + 1, by linarith only [hK], 3 + NB + NG + NP, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : (1 : ℝ) ≤ L := by
    have h := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (show 1 ≤ L by omega)
  have hprofile := (abs_le.mp (hh N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl)).2
  have hbeta := (hb N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl).2
  have herr : (N : ℝ) ^ (-4 / 5 + 1 / 15 : ℝ) ≤ L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (-2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (Nat.cast_nonneg N) (-2 / 3 : ℝ))
        simpa only [one_mul] using h
  exact (PairActivityHostCap.absoluteMass_mono hG L).trans (by linarith only [hprofile, hbeta, herr])

theorem uniform_regular_covariance (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        0 < value N L ∧ |regularCovariance N L| ≤ K * value N L := by
  obtain ⟨p, hp⟩ := uniform_absolute_scale C
  obtain ⟨c, hc, NC, _hNC, hh⟩ := SecondFactorialCorrectionLower.uniform_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨K, hK, NK, _hNK, hk⟩ := hp hgeo
  refine ⟨K / c, div_pos hK hc, 3 + NC + NG + NK, by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (0 : ℝ) < L := by have h := (hg N (by omega) L hband).2.2.1; exact_mod_cast (show 0 < L by omega)
  have hlower := hh N (by omega) L hband
  refine ⟨(mul_pos (mul_pos hc hL) (Real.rpow_pos_of_pos hn _)).trans_le hlower, ?_⟩
  have hcov : |regularCovariance N L| ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) :=
    (PairActivityHostCap.covariance_sum_absolute_bound (RegularStarts.regularStarts N L) L).trans
      (hk N (by omega) L hband _ (RegularStarts.regularStarts_subset N L))
  calc
    _ ≤ K * L * (N : ℝ) ^ (-2 / 3 : ℝ) := hcov
    _ = (K / c) * (c * L * (N : ℝ) ^ (-2 / 3 : ℝ)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower (div_pos hK hc).le

end PaperP1.SharpCovarianceScaleUnderInputs
