module

public import PaperP1.Asymptotics.PrincipalPairPhaseComparison
public import PaperP1.Asymptotics.PairProfiles
public import PaperP1.Model.CountVariance

/-! # Both literal moving-phase equivalents for the actual variance-minus-mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualPairPhase

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.FiniteChannelHierarchy
  PaperP1.ChannelMassPhaseEquivalent PaperP1.PrincipalPairPhaseComparison

local instance : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

def alpha (N L : ℕ) : ℝ :=
  ProbabilityTheory.variance (fun ω ↦ (infiniteStartCount (dyadicBlock N) L ω : ℝ)) infiniteRademacherMeasure -
    ∫ ω, (infiniteStartCount (dyadicBlock N) L ω : ℝ) ∂infiniteRademacherMeasure

theorem alpha_eq_cumulant (N L : ℕ) :
    alpha N L = RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L :=
  (CountVariance.second_cumulant_variance (dyadicBlock N) L).symm

theorem main_sum (N L : ℕ) (hN : 0 < N) :
    ChannelMainTermBounds.mainTerm N L 2 3 + ChannelMainTermBounds.mainTerm N L 3 4 =
      (nominalMean N L) ^ 2 / (3 * N) *
        ((ChannelSumIdentity.signed L 2 3 : ℤ) + (ChannelSumIdentity.signed L 3 4 : ℤ)) := by
  rw [mainTerm_eq_nominal N L 2 3 hN, mainTerm_eq_nominal N L 3 4 hN]
  have h23 : (ActualSourceTranslations.coefficient 2 3 : ℝ) = 1 / 3 := by norm_num [ActualSourceTranslations.coefficient]
  have h34 : (ActualSourceTranslations.coefficient 3 4 : ℝ) = 1 / 3 := by norm_num [ActualSourceTranslations.coefficient]
  rw [h23, h34]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem article_3_3_cumulant (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |alpha N L - (nominalMean N L) ^ 2 / (3 * N) *
          ((ChannelSumIdentity.signed L 2 3 : ℤ) + (ChannelSumIdentity.signed L 3 4 : ℤ))| ≤
          (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨N₀, hN₀, hp⟩ := PairProfiles.uniform_profiles C ε 8 hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have h := (hp N hN L (8 * (L + 1)) hband le_rfl le_rfl).2
  rw [main_sum N L (by omega)] at h
  rw [alpha_eq_cumulant]
  exact h

theorem uniform_phases (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (0 < phaseMass N L 3 ∧ 0 < phaseMass N L 4 ∧
        |alpha N L / phaseMass N L 3 - 1| ≤ ε ∧
        |(alpha N L - ChannelMainTermBounds.mainTerm N L 2 3) / phaseMass N L 4 - 1| ≤ ε) := by
  obtain ⟨NP, _hNP, hp⟩ := PairProfiles.uniform_profiles C (1 / 40) 8 (by norm_num)
  obtain ⟨N3, _hN3, h3⟩ := ChannelMassPhaseEquivalent.uniform_relative C 3 (by decide) (ε / 3) (by positivity)
  obtain ⟨N4, _hN4, h4⟩ := ChannelMassPhaseEquivalent.uniform_relative C 4 (by decide) (ε / 2) (by positivity)
  obtain ⟨NE3, _hNE3, he3⟩ := power_error_negligible C (-31 / 40) 3 (by decide) (by norm_num) (ε / 3) (by positivity)
  obtain ⟨NE4, _hNE4, he4⟩ := power_error_negligible C (-31 / 40) 4 (by decide) (by norm_num) (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := next_channel_negligible C (ε / 3) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
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
  exact ⟨hp3, hp4, ratio_bound hp3 hfirst, ratio_bound hp4 hsecond⟩

theorem article_3_3_phases (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (|alpha N L / ((((L % 3 : ℕ) : ℝ) + 2) /
          (18 * (2 : ℝ) ^ (((L % 3 : ℕ) : ℝ) / 3)) *
          (nominalMean N L) ^ (5 / 3 : ℝ) * L * (N : ℝ) ^ (-2 / 3 : ℝ)) - 1| ≤ ε ∧
        |(alpha N L - (nominalMean N L) ^ 2 / (3 * N) * (ChannelSumIdentity.signed L 2 3 : ℤ)) /
          ((((L % 4 : ℕ) : ℝ) + 3) / (24 * (2 : ℝ) ^ (((L % 4 : ℕ) : ℝ) / 4)) *
          (nominalMean N L) ^ (7 / 4 : ℝ) * L * (N : ℝ) ^ (-3 / 4 : ℝ)) - 1| ≤ ε) := by
  obtain ⟨N₀, hN₀, hp⟩ := uniform_phases C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have h := (hp N hN L hband).2.2
  simpa only [phase_three, phase_four, whole_first_channel N L (by omega)] using h

end PaperP1.ActualPairPhase
