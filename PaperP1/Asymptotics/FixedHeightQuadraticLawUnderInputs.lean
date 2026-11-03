module

public import PaperP1.Asymptotics.FixedHeightCumulantProfileUnderInputs
public import PaperP1.Asymptotics.QuadraticRateOneUnderInputs
public import PaperP1.Asymptotics.AdjacentReferencePhase
public import PaperP1.Asymptotics.PrincipalPairPhaseComparison
public import PaperP1.Probability.PoissonParameterStability

/-! # Actual-law errors and complete moving-phase equivalents at every fixed channel height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHeightQuadraticLawUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent

structure Parameters where
  law : TripleActivityLawReconstructionUnderInputs.Parameters
  profile : FinitePairDeficitInputs.Parameters

structure Hypotheses (p : Parameters) (ε : ℝ) : Prop where
  law : TripleActivityLawReconstructionUnderInputs.Hypotheses p.law (min (ε / 256) (1 / 48))
  profile : FinitePairDeficitInputs.Hypotheses p.profile (GeneralGraphHostCount.sizeCap (ε / 256))

theorem uniform_coarse (h : ℕ) (hh : 3 ≤ h) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h)) ≤
          (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε) := by
  obtain ⟨pl, hl⟩ := QuadraticRateOneUnderInputs.companion_T17_5 C (ε / 2) (by positivity)
  obtain ⟨pp, hp⟩ := FixedHeightCumulantProfileUnderInputs.uniform_coarse h hh C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3
    (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨pl, pp⟩, ?_⟩
  intro hgeo
  obtain ⟨NL, _hNL, hl⟩ := hl (by simpa only [show ε / 2 / 128 = ε / 256 by ring] using hgeo.law)
  obtain ⟨NP, _hNP, hp⟩ := hp (by simpa only [show ε / 2 / 128 = ε / 256 by ring] using hgeo.profile)
  refine ⟨max 2 (max NL (max NP NF)), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let P := (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  let Q := QuadraticPoisson.reference (nominalMean N L) α
  let S := QuadraticPoisson.reference (nominalMean N L) (coefficient N L h)
  have hmean : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hdist : SignedAtomicDistance.distance P Q ≤ (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) :=
    ((hl N (by omega) L hband).2).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by
        have ht : (0 : ℝ) ≤ 1 / ((h + 1 : ℕ) : ℝ) := by positivity
        linarith only [ht]))
  have hcoef := hp N (by omega) L hband
  have hchange : SignedAtomicDistance.distance Q S ≤ 2 * |α - coefficient N L h| := by
    have hb := PoissonParameterStability.actual_signed_difference hmean hmean α (coefficient N L h)
    simpa only [SignedAtomicDistance.distance, _root_.sub_apply, sub_self, abs_zero, mul_zero, zero_add] using hb
  have htriangle := SignedAtomicDistance.triangle P Q S
  calc
    _ ≤ 3 * (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) := by
      linarith only [htriangle, hdist, hchange, hcoef]
    _ ≤ (N : ℝ) ^ ((-1 + 1 / ((h + 1 : ℕ) : ℝ) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem reference_increment (μ α β : ℝ) (hμ : 0 ≤ μ) :
    QuadraticPoisson.reference μ (α + β) = QuadraticPoisson.reference μ α +
      (β / 2) • QuadraticPoisson.differenceMap (QuadraticPoisson.differenceMap (QuadraticPoisson.poissonSigned μ)) := by
  rw [QuadraticPoisson.reference_eq_poisson_plus_secondDifference μ (α + β) hμ,
    QuadraticPoisson.reference_eq_poisson_plus_secondDifference μ α hμ]
  module

theorem distance_sub (P Q S : SignedMeasure ℕ) :
    SignedAtomicDistance.distance (P - Q) S = SignedAtomicDistance.distance P (Q + S) := by
  unfold SignedAtomicDistance.distance
  apply tsum_congr
  intro k
  rw [_root_.sub_apply, _root_.add_apply]
  congr 1
  ring

theorem uniform_next_remainder (h : ℕ) (hh : 3 ≤ h) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p ε →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SignedAtomicDistance.distance
        ((RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure -
          QuadraticPoisson.reference (nominalMean N L) (coefficient N L h))
        ((heightMass N L (h + 1) / 2) • QuadraticPoisson.differenceMap
          (QuadraticPoisson.differenceMap (QuadraticPoisson.poissonSigned (nominalMean N L)))) ≤
        (N : ℝ) ^ (-1 + 1 / ((h + 2 : ℕ) : ℝ) + ε) := by
  obtain ⟨p, hp⟩ := uniform_coarse (h + 1) (by omega) C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh₀⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hbound := hh₀ N hN L hband
  rw [HeightFiveChannelCorrection.coefficient_succ N L h (by omega)] at hbound
  rw [distance_sub, ← reference_increment _ _ _ (by unfold nominalMean; positivity)]
  exact hbound

theorem distance_symm (P Q : SignedMeasure ℕ) :
    SignedAtomicDistance.distance P Q = SignedAtomicDistance.distance Q P := by
  unfold SignedAtomicDistance.distance
  exact tsum_congr fun _ ↦ abs_sub_comm _ _

theorem distance_stability (P Q S : SignedMeasure ℕ) :
    |SignedAtomicDistance.distance P S - SignedAtomicDistance.distance Q S| ≤
      SignedAtomicDistance.distance P Q := by
  have h1 := SignedAtomicDistance.triangle P Q S
  have h2 := SignedAtomicDistance.triangle Q P S
  rw [distance_symm Q P] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

def phaseMargin (h : ℕ) : ℝ := 1 / (2 * ((h + 1 : ℕ) : ℝ) * ((h + 2 : ℕ) : ℝ))

theorem phaseMargin_pos (h : ℕ) : 0 < phaseMargin h := by unfold phaseMargin; positivity

theorem phaseMargin_gap (h : ℕ) :
    -1 + 1 / ((h + 2 : ℕ) : ℝ) + phaseMargin h < -1 + 1 / ((h + 1 : ℕ) : ℝ) := by
  unfold phaseMargin
  have h1 : (0 : ℝ) < ((h + 1 : ℕ) : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((h + 2 : ℕ) : ℝ) := by positivity
  have he : 1 / ((h + 1 : ℕ) : ℝ) - 1 / ((h + 2 : ℕ) : ℝ) =
      1 / (((h + 1 : ℕ) : ℝ) * ((h + 2 : ℕ) : ℝ)) := by push_cast; field_simp; ring
  have hp : (0 : ℝ) < 1 / (((h + 1 : ℕ) : ℝ) * ((h + 2 : ℕ) : ℝ)) := by positivity
  have hh : 1 / (2 * ((h + 1 : ℕ) : ℝ) * ((h + 2 : ℕ) : ℝ)) =
      (1 / (((h + 1 : ℕ) : ℝ) * ((h + 2 : ℕ) : ℝ))) / 2 := by ring
  rw [hh]
  linarith only [he, hp]

theorem power_negligible (h : ℕ) (hh : 3 ≤ h) (C τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ (-1 + 1 / ((h + 2 : ℕ) : ℝ) + phaseMargin h) ≤
        τ * AdjacentReferencePhase.leadingGap N L h := by
  let M := (2 : ℝ) ^ C
  obtain ⟨NP, _hNP, hp⟩ := PrincipalPairPhaseComparison.power_error_negligible C
    (-1 + 1 / ((h + 2 : ℕ) : ℝ) + phaseMargin h) (h + 1) (by omega)
    (phaseMargin_gap h) (τ * Real.exp (-M)) (by positivity)
  obtain ⟨NL, hl⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NP NL), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have hl₀ := (hl N (by omega) L hband).2.2.1; omega
  have hphase := phaseMass_pos N L (h + 1) (by omega) hL (by omega)
  have hnom := (FiniteChannelHierarchyBounds.nominal_bounds (by omega : 2 ≤ N) hband).2
  have hnorm := PoissonSecondDifferenceNorm.norm_second_lower_bound (nominalMean N L)
    (by unfold nominalMean; positivity)
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hnom)
  have hprod := mul_le_mul_of_nonneg_left (show 2 * Real.exp (-M) ≤ PoissonDifferenceSigned.norm (nominalMean N L) 2 by
    linarith only [hexp, hnorm]) (hphase.le)
  have hgap : Real.exp (-M) * phaseMass N L (h + 1) ≤ AdjacentReferencePhase.leadingGap N L h := by
    unfold AdjacentReferencePhase.leadingGap
    nlinarith only [hprod]
  exact (hp N (by omega) L hband).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgap hτ.le)

theorem uniform_relative (h : ℕ) (hh : 3 ≤ h) (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (phaseMargin h) → ∀ τ : ℝ, 0 < τ →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let D := SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
        (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h))
      0 < AdjacentReferencePhase.leadingGap N L h ∧
      |D - AdjacentReferencePhase.leadingGap N L h| ≤ τ * AdjacentReferencePhase.leadingGap N L h := by
  obtain ⟨p, hp⟩ := uniform_coarse (h + 1) (by omega) C (phaseMargin h) (phaseMargin_pos h)
  refine ⟨p, ?_⟩
  intro hgeo τ hτ
  obtain ⟨NC, _hNC, hc⟩ := hp hgeo
  obtain ⟨NR, _hNR, hr⟩ := AdjacentReferencePhase.uniform_relative C h hh (τ / 2) (by positivity)
  obtain ⟨NE, _hNE, he⟩ := power_negligible h hh C (τ / 2) (by positivity)
  refine ⟨max 2 (max NC (max NR NE)), by omega, ?_⟩
  intro N hN L hband
  dsimp only
  obtain ⟨hpos, hreference⟩ := hr N (by omega) L hband
  have herror := (hc N (by omega) L hband).trans (he N (by omega) L hband)
  have hstability := distance_stability
    (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
    (QuadraticPoisson.reference (nominalMean N L) (coefficient N L (h + 1)))
    (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h))
  rw [distance_symm (QuadraticPoisson.reference (nominalMean N L) (coefficient N L (h + 1)))] at hstability
  change |SignedAtomicDistance.distance _ _ - AdjacentReferencePhase.gap N L h| ≤ _ at hstability
  have htriangle := abs_sub_le
    (SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h)))
    (AdjacentReferencePhase.gap N L h) (AdjacentReferencePhase.leadingGap N L h)
  exact ⟨hpos, by linarith only [htriangle, hstability, herror, hreference]⟩

theorem uniform_probability_equivalent (h : ℕ) (hh : 3 ≤ h) (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (phaseMargin h) → ∀ τ : ℝ, 0 < τ →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ Q : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) ∧
        0 < AdjacentReferencePhase.leadingGap N L h ∧
        |AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) Q /
          (AdjacentReferencePhase.leadingGap N L h / 2) - 1| ≤ τ := by
  obtain ⟨p, hp⟩ := uniform_relative h hh C
  obtain ⟨NQ, _hNQ, hq⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  refine ⟨p, ?_⟩
  intro hgeo τ hτ
  obtain ⟨NR, _hNR, hr⟩ := hp hgeo τ hτ
  refine ⟨max 2 (max NR NQ), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨Q, hQ⟩ := (hq N (by omega) L hband).2.2.1
  obtain ⟨hpos, he⟩ := hr N (by omega) L hband
  have hdist := SignedAtomicDistance.probability_eq (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) Q
  rw [hQ] at hdist
  have hratio := PrincipalPairPhaseComparison.ratio_bound hpos he
  rw [hdist] at hratio
  refine ⟨Q, hQ, hpos, ?_⟩
  convert hratio using 1
  congr 2
  field_simp

end PaperP1.FixedHeightQuadraticLawUnderInputs
