module

public import PaperP1.Model.PrincipalChannelEdges
public import PaperP1.Asymptotics.PrivateChannelActivityRate
public import PaperP1.Asymptotics.PairActivityCumulantGap

/-! # The actual two-channel beta has its unconditional phase and one-sided cumulant comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalChannelEdgesPhase

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges
  PaperP1.PrivateChannelSources

theorem uniform_geometry (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 < L ∧ 29 * (L + 1) < N := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 29 (by norm_num) 1
  refine ⟨max 2 (max NG NL), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  refine ⟨hL, ?_⟩
  have h := hl N (by omega) L hband
  simp only [pow_one] at h
  exact_mod_cast h

theorem positive_phase (C : ℝ) (D : ℕ) :
    ∃ c k : ℝ, 0 < c ∧ 0 < k ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      c * L * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ beta N H L ∧
        beta N H L ≤ k * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
  obtain ⟨c23, k23, hc23, hk23, N23, h23⟩ := PrivateChannelMassPhase.positive_phase C D 2 3
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨_c34, k34, _hc34, hk34, N34, h34⟩ := PrivateChannelMassPhase.positive_phase C D 3 4
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨NG, _hNG, hg⟩ := uniform_geometry C
  refine ⟨c23 / 2, (k23 + k34) / 2, by positivity, by positivity, max 2 (max NG (max N23 N34)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hphase23 := h23 N (by omega) L H hband (by omega) hH
  have hphase34 := (h34 N (by omega) L H hband (by omega) hH).2
  norm_num only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 3 = -2 / 3 by ring] at hphase23
  norm_num only [Nat.cast_ofNat, show -(1 : ℝ) + 1 / 4 = -3 / 4 by ring] at hphase34
  have hpow : (N : ℝ) ^ (-3 / 4 : ℝ) ≤ (N : ℝ) ^ (-2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have h34upper : channelMass N H 3 4 L ≤ k34 * L * (N : ℝ) ^ (-2 / 3 : ℝ) :=
    hphase34.trans (mul_le_mul_of_nonneg_left (by simpa only [neg_div] using hpow) (by positivity))
  have h34nonneg : 0 ≤ channelMass N H 3 4 L := sum_nonneg fun e _ ↦ infiniteJointMoment_nonneg L _
  rw [beta_eq (by omega) (hg N (by omega) L hband).2]
  exact ⟨by nlinarith only [hphase23.1, h34nonneg], by nlinarith only [hphase23.2, h34upper]⟩

theorem uniform_activity_gap (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 ≤ beta N H L - CompatibleActivitySplit.absolute L (edges N H L) ∧
        beta N H L - CompatibleActivitySplit.absolute L (edges N H L) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N23, _hN23, h23⟩ := PrivateChannelActivityRate.uniform_independent_mass C (ε / 2) 2 3 (by decide) (by decide) (by positivity)
  obtain ⟨N34, _hN34, h34⟩ := PrivateChannelActivityRate.uniform_independent_mass C (ε / 2) 3 4 (by decide) (by decide) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := uniform_geometry C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NG (max N23 (max N34 NF))), by omega, ?_⟩
  intro N hN L H hband
  obtain ⟨hL, hlarge⟩ := hg N (by omega) L hband
  have hgap := activity_gap (H := H) (by omega) hlarge hL
  refine ⟨hgap.1, ?_⟩
  calc
    _ ≤ PrivateChannelActivity.independentMass N H 2 3 L + PrivateChannelActivity.independentMass N H 3 4 L := hgap.2
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [h23 N (by omega) L H hband, h34 N (by omega) L H hband]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_cumulant_upper_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 * beta N H L - RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ≤
        (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := uniform_activity_gap C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := PairActivityCumulantGapAsymptotic.uniform_gap C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := uniform_geometry C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NB (max NA (max NG NF))), by omega, ?_⟩
  intro N hN L H hband
  have hlarge := (hg N (by omega) L hband).2
  have hsub : CompatibleActivitySplit.absolute L (edges N H L) ≤
      CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) :=
    sum_le_sum_of_subset_of_nonneg (subset_pairs (by omega) hlarge) fun _ _ _ ↦ abs_nonneg _
  have hbeta := (hb N (by omega) L H hband).2
  have hgap := (ha N (by omega) L hband (dyadicBlock N) (subset_refl _)).2
  calc
    _ ≤ 4 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hsub, hbeta, hgap]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrincipalChannelEdgesPhase
