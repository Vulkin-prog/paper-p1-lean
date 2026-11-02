module

public import PaperP1.Asymptotics.AdjacentReferencePhase
public import PaperP1.Asymptotics.ExplicitHermiteComparison
public import PaperP1.Asymptotics.ChannelMassPhaseLower

/-! # Adjacent literal Hermite references have the same leading distance

The two constructed references are compared with each other. No original
count-law remainder, leading equivalent or optimality is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AdjacentHermiteReferencePhase

open MeasureTheory PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent
  PaperP1.AdjacentReferencePhase PaperP1.PoissonDifferenceSigned

theorem uniform_leading_lower (C : ℝ) (h : ℕ) (hh : 3 ≤ h) :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → d / N ≤ leadingGap N L h / 2 := by
  obtain ⟨d, hd, ND, hND, hlower⟩ := ChannelMassPhaseLower.uniform_coarse_lower C (h + 1) (by omega)
  refine ⟨d * Real.exp (-((2 : ℝ) ^ C)) / 2, by positivity, ND, hND, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := hlower N hN L hband
  have hphase : 0 ≤ phaseMass N L (h + 1) := (by positivity : 0 ≤ d / (N : ℝ)).trans hp
  have hmu : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hcap := (FiniteChannelHierarchyBounds.nominal_bounds (by omega : 2 ≤ N) hband).2
  have he := Real.exp_le_exp.mpr (neg_le_neg hcap)
  have hnorm := PoissonSecondDifferenceNorm.norm_second_lower_bound (nominalMean N L) hmu
  have hnorm' : Real.exp (-((2 : ℝ) ^ C)) / 2 ≤ norm (nominalMean N L) 2 / 4 := by
    linarith only [he, hnorm]
  calc
    _ = (d / N) * (Real.exp (-((2 : ℝ) ^ C)) / 2) := by ring
    _ ≤ phaseMass N L (h + 1) * (norm (nominalMean N L) 2 / 4) :=
      mul_le_mul hp hnorm' (by positivity) hphase
    _ = _ := by unfold leadingGap; ring

theorem uniform_probability_gap (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ H K : ProbabilityMeasure ℕ,
        (H : Measure ℕ).toSignedMeasure = CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L h)) ∧
        (K : Measure ℕ).toSignedMeasure = CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L (h + 1))) ∧
        0 < leadingGap N L h ∧ |AtomicProbability.totalVariation H K / (leadingGap N L h / 2) - 1| ≤ ε := by
  obtain ⟨NG, hNG, hgap⟩ := AdjacentReferencePhase.uniform_relative C h hh (ε / 2) (by positivity)
  obtain ⟨NP, hNP, hprob⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  obtain ⟨NR, hNR, hprobR⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C (h + 1) (by omega)
  obtain ⟨NE, hNE, herror⟩ := ExplicitHermiteComparison.uniform_bound C h hh (1 / 12) (by norm_num)
  obtain ⟨NF, hNF, herrorR⟩ := ExplicitHermiteComparison.uniform_bound C (h + 1) (by omega) (1 / 12) (by norm_num)
  obtain ⟨d, hd, ND, hND, hlower⟩ := uniform_leading_lower C h hh
  have hprod : 0 < (ε / 2) * d := by positivity
  obtain ⟨NB, hbudget⟩ := HalfCountSchedule.factor_absorption (1 / ((ε / 2) * d)) (-5 / 4) (1 / 4) (by norm_num)
  refine ⟨max NG (max NP (max NR (max NE (max NF (max ND NB))))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨Q, hQ⟩ := (hprob N (by omega) L hband).2.2.1
  obtain ⟨H, hH⟩ := (hprob N (by omega) L hband).2.2.2
  obtain ⟨R, hR⟩ := (hprobR N (by omega) L hband).2.2.1
  obtain ⟨K, hK⟩ := (hprobR N (by omega) L hband).2.2.2
  obtain ⟨hpos, hrelative⟩ := hgap N (by omega) L hband
  have htv : AtomicProbability.totalVariation Q R = gap N L h / 2 := by
    have hs := AtomicProbabilityMetric.signed_distance Q R
    rw [hQ, hR] at hs
    change gap N L h = 2 * AtomicProbability.totalVariation Q R at hs
    linarith only [hs]
  have heQ : 2 * AtomicProbability.totalVariation Q H ≤ (N : ℝ) ^ (-5 / 4 : ℝ) := by
    have he := herror N (by omega) L hband
    have hs := AtomicProbabilityMetric.signed_distance Q H
    rw [hQ, hH] at hs
    change ExplicitHermiteComparison.signedError N L h = _ at hs
    rw [hs] at he
    convert he using 1; norm_num
  have heR : 2 * AtomicProbability.totalVariation R K ≤ (N : ℝ) ^ (-5 / 4 : ℝ) := by
    have he := herrorR N (by omega) L hband
    have hs := AtomicProbabilityMetric.signed_distance R K
    rw [hR, hK] at hs
    change ExplicitHermiteComparison.signedError N L (h + 1) = _ at hs
    rw [hs] at he
    convert he using 1; norm_num
  have hpair := AtomicProbabilityMetric.pair_stability H K Q R
  rw [AtomicProbability.totalVariation_symm H Q, AtomicProbability.totalVariation_symm K R] at hpair
  have hbound : |AtomicProbability.totalVariation H K - AtomicProbability.totalVariation Q R| ≤
      (N : ℝ) ^ (-5 / 4 : ℝ) := by linarith only [hpair, heQ, heR]
  have hf := hbudget N (by omega)
  norm_num only [show (-5 / 4 : ℝ) + 1 / 4 = -1 by ring] at hf
  have hsmall : (N : ℝ) ^ (-5 / 4 : ℝ) ≤ (ε / 2) * (leadingGap N L h / 2) := by
    have hs := mul_le_mul_of_nonneg_left hf hprod.le
    rw [← mul_assoc, mul_one_div_cancel hprod.ne', one_mul, Real.rpow_neg_one] at hs
    have hl := mul_le_mul_of_nonneg_left (hlower N (by omega) L hband) (by positivity : 0 ≤ ε / 2)
    have hid : ((ε / 2) * d) * (N : ℝ)⁻¹ = (ε / 2) * (d / N) := by ring
    rw [hid] at hs
    simpa only [neg_div] using hs.trans hl
  have hquadratic : |AtomicProbability.totalVariation Q R - leadingGap N L h / 2| ≤
      (ε / 2) * (leadingGap N L h / 2) := by
    rw [htv, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_div_of_nonneg_right hrelative (by norm_num)).trans_eq (by ring)
  have hall : |AtomicProbability.totalVariation H K - leadingGap N L h / 2| ≤ ε * (leadingGap N L h / 2) := by
    have htriangle := abs_sub_le (AtomicProbability.totalVariation H K) (AtomicProbability.totalVariation Q R)
      (leadingGap N L h / 2)
    linarith only [htriangle, hbound, hsmall, hquadratic]
  refine ⟨H, K, hH, hK, hpos, ?_⟩
  have hE : 0 < leadingGap N L h / 2 := by positivity
  have hid : AtomicProbability.totalVariation H K / (leadingGap N L h / 2) - 1 =
      (AtomicProbability.totalVariation H K - leadingGap N L h / 2) / (leadingGap N L h / 2) := by field_simp
  rw [hid, abs_div, abs_of_pos hE]
  exact (div_le_iff₀ hE).mpr hall

end PaperP1.AdjacentHermiteReferencePhase
