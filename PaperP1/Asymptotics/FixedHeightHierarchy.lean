module

public import PaperP1.Asymptotics.FixedHeightQuadraticLaw

/-! # All literal conclusions of the fixed-height hierarchy, with a quantitative optimal-power lower bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHeightHierarchy

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent

theorem source_exponent (h : ℕ) :
    -1 + 1 / ((h + 2 : ℕ) : ℝ) = -((h + 1 : ℕ) : ℝ) / ((h + 2 : ℕ) : ℝ) := by
  push_cast
  field_simp
  ring

theorem uniform_lower_power (h : ℕ) (hh : 3 ≤ h) (C : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      d * (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ)) ≤
        SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
          (QuadraticPoisson.reference (nominalMean N L) (coefficient N L h)) := by
  have hp := FixedHeightQuadraticLaw.uniform_relative h hh C
  obtain ⟨d, hd, ND, _hND, hlower⟩ := ChannelMassPhaseLower.uniform_phase_lower C (h + 1) (by omega)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let M := (2 : ℝ) ^ C
  obtain ⟨NR, _hNR, hr⟩ := hp (1 / 2) (by norm_num)
  refine ⟨Real.exp (-M) * d / 2, by positivity, max 2 (max NR (max ND NG)), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨_hp, hrelative⟩ := hr N (by omega) L hband
  have hL : 0 < L := by have hl := (hg N (by omega) L hband).2.2.1; omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hphase := hlower N (by omega) L hband
  have hphase0 := (phaseMass_pos N L (h + 1) (by omega) hL (by omega)).le
  have hphasebase : d * (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ)) ≤ phaseMass N L (h + 1) := by
    have h := mul_le_mul_of_nonneg_right hL1
      (by positivity : 0 ≤ d * (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ)))
    nlinarith only [hphase, h]
  have hnom := (FiniteChannelHierarchyBounds.nominal_bounds (by omega : 2 ≤ N) hband).2
  have hnorm := PoissonSecondDifferenceNorm.norm_second_lower_bound (nominalMean N L)
    (by unfold nominalMean; positivity)
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hnom)
  have hnorm' : 2 * Real.exp (-M) ≤ PoissonDifferenceSigned.norm (nominalMean N L) 2 := by
    linarith only [hexp, hnorm]
  have hprod := mul_le_mul_of_nonneg_left hnorm' hphase0
  have hl := mul_le_mul_of_nonneg_left hphasebase (Real.exp_pos (-M)).le
  have hgap : Real.exp (-M) * d * (N : ℝ) ^ (-1 + 1 / ((h + 1 : ℕ) : ℝ)) ≤
      AdjacentReferencePhase.leadingGap N L h := by
    unfold AdjacentReferencePhase.leadingGap
    nlinarith only [hprod, hl]
  have htrue := (abs_le.mp hrelative).1
  nlinarith only [htrue, hgap]

theorem article_18_1 (h : ℕ) (hh : 3 ≤ h) (C ε : ℝ) (hε : 0 < ε) :
    ∀ τ : ℝ, 0 < τ →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - coefficient N L h - heightMass N L (h + 1)| ≤
        (N : ℝ) ^ (-((h + 1 : ℕ) : ℝ) / ((h + 2 : ℕ) : ℝ) + ε) ∧
      SignedAtomicDistance.distance
        ((RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure -
          QuadraticPoisson.reference (nominalMean N L) (coefficient N L h))
        ((heightMass N L (h + 1) / 2) • QuadraticPoisson.differenceMap
          (QuadraticPoisson.differenceMap (QuadraticPoisson.poissonSigned (nominalMean N L)))) ≤
        (N : ℝ) ^ (-((h + 1 : ℕ) : ℝ) / ((h + 2 : ℕ) : ℝ) + ε) ∧
      ∃ Q : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) ∧
        0 < AdjacentReferencePhase.leadingGap N L h ∧
        |AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) Q /
          (phaseMass N L (h + 1) * PoissonDifferenceSigned.norm (nominalMean N L) 2 / 4) - 1| ≤ τ := by
  obtain ⟨NC, _hNC, hc⟩ := FixedHeightCumulantProfile.uniform_next_height h hh C ε hε
  obtain ⟨NL, _hNL, hl⟩ := FixedHeightQuadraticLaw.uniform_next_remainder h hh C ε hε
  have hp := FixedHeightQuadraticLaw.uniform_probability_equivalent h hh C
  intro τ hτ
  obtain ⟨NP, _hNP, hp⟩ := hp τ hτ
  refine ⟨max 2 (max NC (max NL NP)), by omega, ?_⟩
  intro N hN L hband
  have hcum := hc N (by omega) L hband
  have hlaw := hl N (by omega) L hband
  rw [source_exponent] at hcum hlaw
  obtain ⟨Q, hQ, hpos, heq⟩ := hp N (by omega) L hband
  refine ⟨hcum, hlaw, Q, hQ, hpos, ?_⟩
  have hdenom : AdjacentReferencePhase.leadingGap N L h / 2 =
      phaseMass N L (h + 1) * PoissonDifferenceSigned.norm (nominalMean N L) 2 / 4 := by
    unfold AdjacentReferencePhase.leadingGap
    ring
  rwa [hdenom] at heq

end PaperP1.FixedHeightHierarchy
