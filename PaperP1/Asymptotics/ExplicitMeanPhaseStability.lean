module

public import PaperP1.Asymptotics.ActualNominalReferenceComparison
public import PaperP1.Asymptotics.ActualReferenceAdmissibility
public import PaperP1.Asymptotics.ExplicitReferenceAdmissibility
public import PaperP1.Asymptotics.ChannelMassPhaseLower
public import PaperP1.Probability.AtomicProbabilityMetric

/-! # The exact-to-nominal mean change is negligible at every fixed omitted height

The literal finite coefficient is kept fixed. All probability witnesses
and thresholds are proved without BCN or a count-law approximation input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitMeanPhaseStability

open MeasureTheory PaperP1.Model PaperP1.CountObservables
  PaperP1.FiniteChannelHierarchy PaperP1.FiniteChannelHierarchyBounds
  PaperP1.ChannelMassPhaseEquivalent

theorem uniform_actual_mean_probabilities (C : ℝ) (h : ℕ) (hh : 3 ≤ h) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < coefficient N L h ∧ coefficient N L h < countMoment (dyadicBlock N) L 1 ∧
      AtomicSignedLaw.IsProbability (QuadraticPoisson.reference
        (countMoment (dyadicBlock N) L 1) (coefficient N L h)) ∧
      AtomicSignedLaw.IsProbability (CompletedLaw.toSignedMeasure (HermiteReference.reference
        (countMoment (dyadicBlock N) L 1) (coefficient N L h))) := by
  let m := CriticalActualMean.lowerMean C
  let M := 2 * (2 : ℝ) ^ C
  let δ := min m (m ^ 2 / (M + 1)) / 2
  have hm : 0 < m := CriticalActualMean.lowerMean_pos C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NS, hNS, hsmall⟩ := uniform_small C h hh δ hδ
  obtain ⟨NP, hNP, hpositive⟩ := uniform_positive C h hh
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  refine ⟨max NS (max NP NM), by omega, ?_⟩
  intro N hN L hband
  have ha := hpositive N (by omega) L hband
  have hs := hsmall N (by omega) L hband
  obtain ⟨hml, hmu⟩ := hmean N (by omega) L hband
  have hδm : δ < m := by
    have h := min_le_left m (m ^ 2 / (M + 1))
    dsimp [δ]
    linarith only [h, hm]
  have hδcap : δ ≤ m ^ 2 / (M + 1) := by
    have h := min_le_right m (m ^ 2 / (M + 1))
    have hp : 0 ≤ m ^ 2 / (M + 1) := by positivity
    dsimp [δ]
    linarith only [h, hp]
  have hagap : coefficient N L h < countMoment (dyadicBlock N) L 1 :=
    hs.trans_lt (hδm.trans_le hml)
  refine ⟨ha, hagap, ActualReferenceAdmissibility.quadratic_of_bounds hm hM hml hmu ha.le
    (hs.trans hδcap), ?_⟩
  refine ⟨HermiteReference.law _ _ ha.le hagap.le, ?_⟩
  exact (HermiteReference.actual_signed_reference _ _ ha.le hagap.le).symm

theorem uniform_signed_phase (C : ℝ) (b : ℕ) (hb : 3 ≤ b)
    (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < phaseMass N L b ∧ ∀ α : ℝ, |α| ≤ A →
        ActualNominalReferenceComparison.distance N L α ≤ ε * phaseMass N L b := by
  let η : ℝ := 1 / (2 * (b : ℝ))
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NU, hNU, hupper⟩ := ActualNominalReferenceComparison.uniform_upper C A hA η hη
  obtain ⟨d, hd, ND, hND, hlower⟩ := ChannelMassPhaseLower.uniform_phase_lower C b hb
  have hprod : 0 < ε * d := mul_pos hε hd
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (1 / (ε * d)) (-1 + η) η hη
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NU (max ND (max NF NG)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hl : d * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ phaseMass N L b := by
    have h := hlower N (by omega) L hband
    have hp : 0 ≤ d * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by positivity
    nlinarith only [h, mul_le_mul_of_nonneg_left hL1 hp]
  refine ⟨(by positivity : 0 < d * (N : ℝ) ^ (-1 + 1 / (b : ℝ))).trans_le hl, ?_⟩
  intro α hα
  have hf := hfactor N (by omega)
  have hexp : (-1 + η) + η = -1 + 1 / (b : ℝ) := by dsimp [η]; ring
  rw [hexp] at hf
  have hbudget : (N : ℝ) ^ (-1 + η) ≤ (ε * d) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
    have hs := mul_le_mul_of_nonneg_left hf hprod.le
    rw [← mul_assoc, mul_one_div_cancel hprod.ne', one_mul] at hs
    exact hs
  calc
    _ ≤ (N : ℝ) ^ (-1 + η) := hupper N (by omega) L hband α hα
    _ ≤ (ε * d) * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := hbudget
    _ = ε * (d * (N : ℝ) ^ (-1 + 1 / (b : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hε.le

theorem uniform_reference_stability (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ Q R : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference
          (countMoment (dyadicBlock N) L 1) (coefficient N L h) ∧
        (R : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference
          (nominalMean N L) (coefficient N L h) ∧
        0 < phaseMass N L (h + 1) ∧ ∀ P : ProbabilityMeasure ℕ,
          |AtomicProbability.totalVariation P Q - AtomicProbability.totalVariation P R| ≤
            ε * phaseMass N L (h + 1) := by
  obtain ⟨NA, hNA, hactual⟩ := uniform_actual_mean_probabilities C h hh
  obtain ⟨NN, hNN, hnominal⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  obtain ⟨NS, hNS, hsmall⟩ := uniform_small C h hh 1 (by norm_num)
  obtain ⟨NE, hNE, herror⟩ := uniform_signed_phase C (h + 1) (by omega) 1 (by norm_num) ε hε
  refine ⟨max NA (max NN (max NS NE)), by omega, ?_⟩
  intro N hN L hband
  have ha := hactual N (by omega) L hband
  obtain ⟨Q, hQ⟩ := ha.2.2.1
  obtain ⟨R, hR⟩ := (hnominal N (by omega) L hband).2.2.1
  obtain ⟨hphase, he⟩ := herror N (by omega) L hband
  have heα := he (coefficient N L h) (by
    rw [abs_of_nonneg ha.1.le]
    exact hsmall N (by omega) L hband)
  refine ⟨Q, R, hQ, hR, hphase, ?_⟩
  intro P
  have hs := AtomicProbabilityMetric.reference_stability_signed P Q R
  rw [hQ, hR] at hs
  change _ ≤ ActualNominalReferenceComparison.distance N L (coefficient N L h) / 2 at hs
  have hnonneg : 0 ≤ ActualNominalReferenceComparison.distance N L (coefficient N L h) :=
    tsum_nonneg fun _ ↦ abs_nonneg _
  linarith only [hs, heα, hnonneg]

end PaperP1.ExplicitMeanPhaseStability
