module

public import PaperP1.Asymptotics.PoissonScaleRates
public import PaperP1.Asymptotics.FixedPairPhase
public import PaperP1.Probability.PoissonDistanceExpansion

/-! # The exact total-variation scale for both specified Poisson means

Both error powers and the literal moving residue-class equivalent are proved.
Every estimate is supplied internally before each relative tolerance. The equivalent for
the actual-mean Poisson reference has the same nominal moving denominator.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactPoissonScale

open Finset MeasureTheory PaperP1.Model PaperP1.CountObservables PaperP1.FiniteChannelHierarchy
  PaperP1.ChannelMassPhaseEquivalent PaperP1.PoissonDifferenceSigned

def actualPoisson (N L : ℕ) : ProbabilityMeasure ℕ := QuadraticPoisson.poissonLaw
  (countMoment (dyadicBlock N) L 1) (ActualNominalReferenceComparison.actual_mean_nonneg N L)

def nominalPoisson (N L : ℕ) : ProbabilityMeasure ℕ :=
  QuadraticPoisson.poissonLaw (nominalMean N L) (by unfold nominalMean; positivity)

def actualTV (N L : ℕ) : ℝ := AtomicProbability.totalVariation
  (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) (actualPoisson N L)

def nominalTV (N L : ℕ) : ℝ := AtomicProbability.totalVariation
  (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) (nominalPoisson N L)

def phaseScale (N L : ℕ) : ℝ := phaseMass N L 3 * norm (nominalMean N L) 2 / 4

theorem phaseScale_formula (N L : ℕ) : phaseScale N L =
    (((L % 3 : ℕ) : ℝ) + 2) / (72 * (2 : ℝ) ^ (((L % 3 : ℕ) : ℝ) / 3)) *
      (nominalMean N L) ^ (5 / 3 : ℝ) * norm (nominalMean N L) 2 * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
  rw [phaseScale, PrincipalPairPhaseComparison.phase_three]
  ring

theorem article_1_2
    (C ε : ℝ) (hε : 0 < ε) :
    (∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        |actualTV N L - RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 4 *
          norm (countMoment (dyadicBlock N) L 1) 2| ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
        |nominalTV N L - RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 4 *
          norm (nominalMean N L) 2| ≤ (N : ℝ) ^ (-1 + ε)) ∧
      (∀ τ : ℝ, 0 < τ → ∃ N₁ : ℕ, 10 ≤ N₁ ∧ ∀ N ≥ N₁, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        0 < phaseScale N L ∧ |nominalTV N L / phaseScale N L - 1| ≤ τ ∧
          |actualTV N L / phaseScale N L - 1| ≤ τ) := by
  obtain ⟨NR, _hNR, hr⟩ := PoissonScaleRates.uniform_rates C ε hε
  have hp := FixedPairPhase.uniform_errors C
  have hnom (N L : ℕ) (hα : 0 ≤ RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L) :
      |nominalTV N L - RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 4 *
        norm (nominalMean N L) 2| ≤ OptimalNominalQuadratic.nominalError N L / 2 :=
    PoissonDistanceExpansion.finite_expansion _ _ _ (by unfold nominalMean; positivity) hα
  refine ⟨?_, ?_⟩
  · refine ⟨max 10 NR, by omega, ?_⟩
    intro N hN L hband
    obtain ⟨hα, _hα1, ha, hn, _hfixed, _hbias⟩ := hr N (by omega) L hband
    have hactual := PoissonDistanceExpansion.finite_expansion
      (RetainedModifiedLaw.originalLaw (dyadicBlock N) L) (countMoment (dyadicBlock N) L 1)
      (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L)
      (ActualNominalReferenceComparison.actual_mean_nonneg N L) hα
    have hnominal := hnom N L hα
    constructor
    · have hnn := Real.rpow_nonneg (Nat.cast_nonneg N) (-4 / 3 + ε)
      change |actualTV N L - _| ≤ _ at hactual
      change _ ≤ PoissonScaleRates.actualError N L / 2 at hactual
      linarith only [hactual, ha, hnn]
    · have hnn := Real.rpow_nonneg (Nat.cast_nonneg N) (-1 + ε)
      linarith only [hnominal, hn, hnn]
  · intro τ hτ
    let χ := Real.exp (-((2 : ℝ) ^ C)) / 2
    have hχ : 0 < χ := by dsimp [χ]; positivity
    obtain ⟨NP, _hNP, hp⟩ := hp (τ / 3) (by positivity)
    obtain ⟨NE, _hNE, he⟩ := PrincipalPairPhaseComparison.power_error_negligible C (-11 / 12) 3
      (by decide) (by norm_num) (τ / 3 * χ) (by positivity)
    refine ⟨max 10 (max NR (max NP NE)), by omega, ?_⟩
    intro N hN L hband
    obtain ⟨hα, _hα1, _ha, _hn, hfixed, hbias⟩ := hr N (by omega) L hband
    obtain ⟨hphase, _hphase4, herror, _herror4⟩ := hp N (by omega) L hband
    let S := phaseScale N L
    let A := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L / 4 * norm (nominalMean N L) 2
    have hμ : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
    have hnorm := PoissonSecondDifferenceNorm.norm_second_lower_bound (nominalMean N L) hμ
    have hnorm0 : 0 ≤ norm (nominalMean N L) 2 := (by positivity : 0 ≤ 2 * Real.exp (-(nominalMean N L))).trans hnorm
    have hmuCap : nominalMean N L ≤ (2 : ℝ) ^ C := (FiniteChannelHierarchyBounds.nominal_bounds (by omega) hband).2
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hmuCap)
    have hlower : χ * phaseMass N L 3 ≤ S := by
      have hh := mul_le_mul_of_nonneg_right hnorm hphase.le
      have hh' := mul_le_mul_of_nonneg_right hexp hphase.le
      dsimp only [χ, S, phaseScale]
      nlinarith only [hh, hh']
    have hS : 0 < S := (mul_pos hχ hphase).trans_le hlower
    have hsmall : (N : ℝ) ^ (-11 / 12 : ℝ) ≤ τ / 3 * S := by
      have hh := he N (by omega) L hband
      have hh' := mul_le_mul_of_nonneg_left hlower (by positivity : (0 : ℝ) ≤ τ / 3)
      linarith only [hh, hh']
    rw [ActualPairPhase.alpha_eq_cumulant] at herror
    have hleading : |A - S| ≤ τ / 3 * S := by
      have hh := mul_le_mul_of_nonneg_right herror (div_nonneg hnorm0 (by norm_num : (0 : ℝ) ≤ 4))
      have hid : A - S = (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - phaseMass N L 3) *
          (norm (nominalMean N L) 2 / 4) := by dsimp [A, S, phaseScale]; ring
      rw [hid, abs_mul, abs_of_nonneg (div_nonneg hnorm0 (by norm_num : (0 : ℝ) ≤ 4))]
      exact hh.trans_eq (by dsimp [S, phaseScale]; ring)
    have hnominal := hnom N L hα
    change |nominalTV N L - A| ≤ OptimalNominalQuadratic.nominalError N L / 2 at hnominal
    have hτS : 0 ≤ τ * S := mul_nonneg hτ.le hS.le
    have htn := abs_sub_le (nominalTV N L) A S
    have hnerror : |nominalTV N L - S| ≤ τ * S := by
      linarith only [htn, hnominal, hleading, hfixed, hsmall, hτS]
    have hmean := PoissonDistanceExpansion.finite_mean_change (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
      (countMoment (dyadicBlock N) L 1) (nominalMean N L)
      (ActualNominalReferenceComparison.actual_mean_nonneg N L) hμ
    change |actualTV N L - nominalTV N L| ≤ OptimalNominalQuadratic.meanGap N L at hmean
    have hta := abs_sub_le (actualTV N L) (nominalTV N L) S
    have haerror : |actualTV N L - S| ≤ τ * S := by
      linarith only [hta, htn, hmean, hbias, hnominal, hleading, hfixed, hsmall, hτS]
    exact ⟨hS, PrincipalPairPhaseComparison.ratio_bound hS hnerror,
      PrincipalPairPhaseComparison.ratio_bound hS haerror⟩

end PaperP1.ExactPoissonScale
