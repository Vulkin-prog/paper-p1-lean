module

public import PaperP1.Asymptotics.FixedHeightPrivateChannelProfile
public import PaperP1.Asymptotics.FinitePairActivityInputs
public import PaperP1.Asymptotics.ChannelMassPhaseEquivalent
public import PaperP1.Arithmetic.HeightFiveChannelCorrection

/-! # Every fixed-height truncation of the actual second cumulant has its source remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHeightCumulantProfileUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteAlignedChannelCover

theorem uniform_coarse (Q : ℕ) (hQ : 3 ≤ Q) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 128)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
        FiniteChannelHierarchy.coefficient N L Q| ≤ (N : ℝ) ^ (-1 + 1 / ((Q + 1 : ℕ) : ℝ) + ε) := by
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨D, j, j₁, j₂, hD, he⟩ := FiniteGoodPartitionUnderInputs.uniform_exceptional Q C (ε / 2) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := LogHeightAlignedActivity.uniform_bound (Q + 1) (by omega) C (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := FixedHeightPrivateChannelProfile.uniform_comparison Q hQ C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := FixedHeightPrivateChannelProfile.uniform_geometry Q hQ C
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (5 + M ^ 2)
    (-1 + 1 / ((Q + 1 : ℕ) : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨D, j, j₁, j₂, hD⟩, ?_⟩
  intro hgeo
  have hs : (ε / 2) / 64 = ε / 128 := by ring
  obtain ⟨NE, _hNE, he⟩ := he (by simpa only [hs] using hgeo.source)
    hgeo.ordinaryTwo hgeo.ordinaryThree hgeo.sourceCurves hgeo.ordinaryTwoCurves hgeo.ordinaryThreeCurves
  refine ⟨max 2 (max NE (max NW (max NP (max NG (max NL (max NM NF)))))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hl N (by omega) L hband).2.2.1; omega
  have hsmall := (hg N (by omega) L hband).1
  let V := (N : ℝ) ^ (-1 + 1 / ((Q + 1 : ℕ) : ℝ) + ε / 2)
  have hpower : (N : ℝ) ^ (-1 + ε / 2) ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      have hi : (0 : ℝ) ≤ 1 / ((Q + 1 : ℕ) : ℝ) := by positivity
      linarith only [hi])
  have hweak : CompatibleActivitySplit.absolute L (FiniteGoodChannelPartition.weak Q N (2 * Q * (L + 1)) L) ≤ V :=
    (sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans inter_subset_right)
      (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans (hw N (by omega) L hband)
  have hex := (he N (by omega) L hband).trans hpower
  have hprivate := (hp N (by omega) L hband).trans hpower
  have hrest := FixedHeightPrivateChannels.signed_remainder_bound (H := 2 * Q * (L + 1)) (by omega : 2 ≤ N) hL hsmall
  have hdiag : (∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2) ≤ M ^ 2 * V := by
    have hd := SecondCumulantUnderBCN.diagonal_bound (L := L) (by omega : 0 < N) (subset_refl (dyadicBlock N))
      (fun x hx ↦ hm N (by omega) L hband x hx)
    calc
      _ ≤ M ^ 2 / N := hd
      _ = M ^ 2 * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε] : (-1 : ℝ) ≤ -1 + ε / 2)).trans hpower) (sq_nonneg M)
  have hdiag0 : 0 ≤ ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 := sum_nonneg fun x _ ↦ sq_nonneg _
  have hformula := HeterogeneousRunConversion.second_cumulant_formula (L := L) (subset_refl (dyadicBlock N))
  change RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L =
    2 * CompatibleActivitySplit.signed L ((dyadicBlock N).powersetCard 2) -
      ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 at hformula
  have hV : 0 ≤ V := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hfinite : |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
      FiniteChannelHierarchy.coefficient N L Q| ≤ (5 + M ^ 2) * V := by
    rw [hformula]
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hrest).1, hweak, hex, (abs_le.mp hprivate).1, hdiag],
      by linarith only [(abs_le.mp hrest).2, hweak, hex, (abs_le.mp hprivate).2, hdiag0, mul_nonneg (sq_nonneg M) hV]⟩
  calc
    _ ≤ _ := hfinite
    _ ≤ (N : ℝ) ^ ((-1 + 1 / ((Q + 1 : ℕ) : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_next_height (h : ℕ) (hh : 3 ≤ h) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 128)) →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L -
        FiniteChannelHierarchy.coefficient N L h - ChannelMassPhaseEquivalent.heightMass N L (h + 1)| ≤
          (N : ℝ) ^ (-1 + 1 / ((h + 2 : ℕ) : ℝ) + ε) := by
  obtain ⟨p, hp⟩ := uniform_coarse (h + 1) (by omega) C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh₀⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hbound := hh₀ N hN L hband
  rw [HeightFiveChannelCorrection.coefficient_succ N L h (by omega)] at hbound
  simpa only [ChannelMassPhaseEquivalent.heightMass, sub_sub] using hbound

end PaperP1.FixedHeightCumulantProfileUnderInputs
