module

public import PaperP1.Asymptotics.PolynomialWeightedQuadraticUnderInputs
public import PaperP1.Asymptotics.OptimalNominalQuadraticUnderInputs

/-! # One geometric bundle for Poisson expansion errors and a strict phase remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonScaleRatesUnderInputs

open Finset MeasureTheory PaperP1.Model PaperP1.CountObservables PaperP1.FiniteChannelHierarchy
  PaperP1.PolynomialWeightedQuadraticUnderInputs PaperP1.ActualQuadraticSubpowerMoments
  PaperP1.OptimalNominalQuadraticUnderInputs

def actualError (N L : ℕ) : ℝ := SignedAtomicDistance.distance
  (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1)
    (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L))

theorem uniform_rates (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, 1 ≤ p.channelHeight ∧ (Hypotheses p (min (ε / 2) (1 / 12)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        0 ≤ RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ∧
        |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L| ≤ 1 ∧
        actualError N L ≤ (N : ℝ) ^ (-4 / 3 + ε) ∧
        nominalError N L ≤ (N : ℝ) ^ (-1 + ε) ∧
        nominalError N L ≤ (N : ℝ) ^ (-11 / 12 : ℝ) ∧
        meanGap N L ≤ (N : ℝ) ^ (-11 / 12 : ℝ)) := by
  let η := min (ε / 2) (1 / 12)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hηcap : η ≤ 1 / 12 := min_le_right _ _
  obtain ⟨p, hQ, hw⟩ := uniform_weighted c κ hc hBCN C η hη
  obtain ⟨NS, _hNS, hs⟩ := SecondCumulantUnderBCN.uniform_eventually_small c κ hc hBCN C 1 (by norm_num)
  obtain ⟨NP, _hNP, hp⟩ := PositiveSecondCumulant.uniform_positive C
  obtain ⟨NR, _hNR, hr⟩ := ActualNominalReferenceComparison.uniform_upper C 1 (by norm_num) (ε / 2) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := ActualNominalReferenceComparison.uniform_upper C 1 (by norm_num) (1 / 24) (by norm_num)
  obtain ⟨NB, _hNB, hb⟩ := CriticalActualMean.uniform_nominal_bias C (1 / 24) (by norm_num)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := HalfCountSchedule.factor_absorption 2 (-23 / 24) (1 / 24) (by norm_num)
  obtain ⟨NH, hh⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C) (-23 / 24) (1 / 24) (by norm_num)
  refine ⟨p, hQ, ?_⟩
  intro hgeo
  obtain ⟨NW, _hNW, hw⟩ := hw hgeo 0
  refine ⟨max 10 (max NW (max NS (max NP (max NR (max NT (max NB (max NF (max NG NH)))))))), by omega, ?_⟩
  intro N hN L hband
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  have hα : |α| ≤ 1 := hs N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hactual : actualError N L ≤ (N : ℝ) ^ (-4 / 3 + η) := by
    have hμ := ActualNominalReferenceComparison.actual_mean_nonneg N L
    rw [actualError, FourthCharlierLawDistance.distance_eq_sequence _ _ _ hμ]
    simpa only [weightedError, pow_zero, one_mul, original, quadratic] using (hw N (by omega) L hband).2
  have hrule (δ : ℝ) (hd : ActualNominalReferenceComparison.distance N L α ≤ (N : ℝ) ^ δ) :
      nominalError N L ≤ actualError N L + (N : ℝ) ^ δ := by
    have hh := SignedAtomicDistance.triangle
      (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
      (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1) α)
      (QuadraticPoisson.reference (nominalMean N L) α)
    have hid : SignedAtomicDistance.distance
        (QuadraticPoisson.reference (countMoment (dyadicBlock N) L 1) α)
        (QuadraticPoisson.reference (nominalMean N L) α) = ActualNominalReferenceComparison.distance N L α := by
      unfold SignedAtomicDistance.distance ActualNominalReferenceComparison.distance
      simp only [_root_.sub_apply]
    rw [hid] at hh
    exact hh.trans (add_le_add le_rfl hd)
  have heps := hrule (-1 + ε / 2) (hr N (by omega) L hband α hα)
  have hfixed := hrule (-23 / 24) (by
    simpa only [show (-1 : ℝ) + 1 / 24 = -23 / 24 by ring] using ht N (by omega) L hband α hα)
  have hsmallε : actualError N L ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    hactual.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηε]))
  have hsmall : actualError N L ≤ (N : ℝ) ^ (-23 / 24 : ℝ) :=
    hactual.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηcap]))
  refine ⟨(hp N (by omega) L hband).le, hα,
    hactual.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηε, hε])), ?_, ?_, ?_⟩
  · have hf := hf N (by omega)
    rw [show (-1 + ε / 2) + ε / 2 = -1 + ε by ring] at hf
    linarith only [heps, hsmallε, hf]
  · have hg := hg N (by omega)
    rw [show (-23 / 24 : ℝ) + 1 / 24 = -11 / 12 by ring] at hg
    linarith only [hfixed, hsmall, hg]
  · have hb := hb N (by omega) L hband
    change meanGap N L ≤ _ at hb
    rw [show (-1 : ℝ) + 1 / 24 = -23 / 24 by ring] at hb
    exact hb.trans (by simpa only [show (-23 / 24 : ℝ) + 1 / 24 = -11 / 12 by ring] using hh N (by omega))

end PaperP1.PoissonScaleRatesUnderInputs
