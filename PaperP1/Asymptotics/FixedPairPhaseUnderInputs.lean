module

public import PaperP1.Asymptotics.ActualPairPhaseUnderInputs
public import PaperP1.Asymptotics.FinitePairDeficitInputs

/-! # A single finite geometric bundle for both moving pair phases

The bundle is chosen before every relative-error tolerance. The two residues
are the actual moving L mod 3 and L mod 4; no subsequence is selected.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPairPhaseUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteChannelHierarchy
  PaperP1.ChannelMassPhaseEquivalent PaperP1.PrincipalPairPhaseComparison
  PaperP1.ActualPairPhaseUnderInputs

theorem uniform_errors (C : ℝ) :
    ∃ p : FinitePairDeficitInputs.Parameters,
      FinitePairDeficitInputs.Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        0 < phaseMass N L 3 ∧ 0 < phaseMass N L 4 ∧
        |alpha N L - phaseMass N L 3| ≤ ε * phaseMass N L 3 ∧
        |(alpha N L - ChannelMainTermBounds.mainTerm N L 2 3) - phaseMass N L 4| ≤
          ε * phaseMass N L 4 := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hprofile⟩ := PairProfilesUnderGeometricInputs.uniform_profiles C (1 / 40) 8 (by norm_num)
  refine ⟨⟨Ds, k, k₁, k₂, hDs⟩, ?_⟩
  intro hgeo ε hε
  obtain ⟨N3, _hN3, h3⟩ := ChannelMassPhaseEquivalent.uniform_relative C 3 (by decide) (ε / 3) (by positivity)
  obtain ⟨N4, _hN4, h4⟩ := ChannelMassPhaseEquivalent.uniform_relative C 4 (by decide) (ε / 2) (by positivity)
  obtain ⟨NE3, _hNE3, he3⟩ := power_error_negligible C (-31 / 40) 3 (by decide) (by norm_num) (ε / 3) (by positivity)
  obtain ⟨NE4, _hNE4, he4⟩ := power_error_negligible C (-31 / 40) 4 (by decide) (by norm_num) (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := next_channel_negligible C (ε / 3) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, _hNP, hp⟩ := hprofile hgeo.source hgeo.ordinaryTwo hgeo.ordinaryThree hgeo.sourceCurves hgeo.ordinaryTwoCurves hgeo.ordinaryThreeCurves
  refine ⟨max 2 (max NP (max N3 (max N4 (max NE3 (max NE4 (max NT NG)))))), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hp3 := phaseMass_pos N L 3 (by omega) hL (by decide)
  have hp4 := phaseMass_pos N L 4 (by omega) hL (by decide)
  let A := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let M3 := ChannelMainTermBounds.mainTerm N L 2 3
  let M4 := ChannelMainTermBounds.mainTerm N L 3 4
  let P3 := phaseMass N L 3
  let P4 := phaseMass N L 4
  have herror : |A - (M3 + M4)| ≤ (N : ℝ) ^ (-31 / 40 : ℝ) := by
    have h := (hp N (by omega) L (8 * (L + 1)) hband le_rfl le_rfl).2
    rwa [show (-4 / 5 : ℝ) + 1 / 40 = -31 / 40 by ring] at h
  have hm3 := h3 N (by omega) L hband
  have hm4 := h4 N (by omega) L hband
  rw [height_three N L (by omega)] at hm3
  rw [height_four N L (by omega)] at hm4
  have herr3 : |A - (M3 + M4)| ≤ ε / 3 * P3 := herror.trans (he3 N (by omega) L hband)
  have herr4 : |A - (M3 + M4)| ≤ ε / 2 * P4 := herror.trans (he4 N (by omega) L hband)
  have htail := ht N (by omega) L hband
  have hfirst : |A - P3| ≤ ε * P3 := by
    have hT1 := abs_add_le (A - (M3 + M4)) (M3 - P3)
    have hT2 := abs_add_le ((A - (M3 + M4)) + (M3 - P3)) M4
    rw [show (A - (M3 + M4) + (M3 - P3)) + M4 = A - P3 by ring] at hT2
    linarith only [hT1, hT2, herr3, hm3, htail]
  have hsecond : |(A - M3) - P4| ≤ ε * P4 := by
    have hT := abs_sub_le (A - M3) M4 P4
    rw [show (A - M3) - M4 = A - (M3 + M4) by ring] at hT
    linarith only [hT, herr4, hm4]
  rw [alpha_eq_cumulant]
  exact ⟨hp3, hp4, hfirst, hsecond⟩

end PaperP1.FixedPairPhaseUnderInputs
