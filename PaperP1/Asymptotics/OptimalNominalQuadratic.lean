module

public import PaperP1.Asymptotics.PolynomialWeightedQuadratic
public import PaperP1.Asymptotics.ActualNominalReferenceComparison
public import PaperP1.Probability.QuadraticMeanLawComparison

/-! # The full quantized mean-bias proposition for the original law

The same exact second cumulant is used for both quadratic references. The
comparison is internal and applies at every sufficiently large scale where the integer bias is
nonzero, with no assertion that such scales occur infinitely often.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalNominalQuadratic

open Finset MeasureTheory PaperP1.Model PaperP1.CountObservables PaperP1.FiniteChannelHierarchy
  PaperP1.PolynomialWeightedQuadratic PaperP1.ActualQuadraticSubpowerMoments

def meanGap (N L : ℕ) : ℝ := |countMoment (dyadicBlock N) L 1 - nominalMean N L|

def nominalError (N L : ℕ) : ℝ := SignedAtomicDistance.distance
  (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  (QuadraticPoisson.reference (nominalMean N L) (RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L))

def lowerConstant (C : ℝ) : ℝ := Real.exp (-(2 * (2 : ℝ) ^ C)) / 4

theorem lowerConstant_pos (C : ℝ) : 0 < lowerConstant C := by unfold lowerConstant; positivity

theorem uniform_comparison
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        nominalError N L ≤ (N : ℝ) ^ (-1 + ε) ∧
        (MeanBiasQuantization.bias (dyadicBlock N) L ≠ 0 →
          lowerConstant C * meanGap N L ≤ nominalError N L ∧
            nominalError N L ≤ (6 + lowerConstant C) * meanGap N L) := by
  let a := lowerConstant C
  let q := ((2 : ℝ) ^ C)⁻¹
  let η := a * q
  have ha : 0 < a := lowerConstant_pos C
  have hq : 0 < q := by dsimp [q]; positivity
  have hη : 0 < η := mul_pos ha hq
  have hw := uniform_weighted C (1 / 12) (by norm_num)
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NS, _hNS, hs⟩ := SecondCumulant.uniform_eventually_small C 1 (by norm_num)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NR, _hNR, hr⟩ := ActualNominalReferenceComparison.uniform_upper C 1 (by norm_num) (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NE, he⟩ := HalfCountSchedule.factor_absorption η⁻¹ (-5 / 4) (1 / 4) (by norm_num)
  obtain ⟨NW, _hNW, hw⟩ := hw 0
  refine ⟨max 10 (max NW (max NM (max NS (max NG (max NR (max NF NE)))))), by omega, ?_⟩
  intro N hN L hband
  let μ := countMoment (dyadicBlock N) L 1
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let P := (RetainedModifiedLaw.originalLaw (dyadicBlock N) L : Measure ℕ).toSignedMeasure
  let Qμ := QuadraticPoisson.reference μ α
  let Qν := QuadraticPoisson.reference (nominalMean N L) α
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hμ : 0 ≤ μ := ActualNominalReferenceComparison.actual_mean_nonneg N L
  have hν : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hα : |α| ≤ 1 := hs N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hL : 0 < L := by have hh := (hg N (by omega) L hband).2.2.1; omega
  have hactual : SignedAtomicDistance.distance P Qμ ≤ (N : ℝ) ^ (-5 / 4 : ℝ) := by
    have hh := (hw N (by omega) L hband).2
    simp only [weightedError, pow_zero, one_mul] at hh
    rw [FourthCharlierLawDistance.distance_eq_sequence _ _ _ hμ]
    simpa only [original, quadratic, show (-4 / 3 : ℝ) + 1 / 12 = -5 / 4 by ring] using hh
  have hreference : SignedAtomicDistance.distance Qμ Qν ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    have hh := hr N (by omega) L hband α hα
    simpa only [ActualNominalReferenceComparison.distance, SignedAtomicDistance.distance, _root_.sub_apply] using hh
  have htri := SignedAtomicDistance.triangle P Qμ Qν
  refine ⟨?_, ?_⟩
  · have hsmall : (N : ℝ) ^ (-5 / 4 : ℝ) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])
    have hh : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
      simpa only [show (-1 + ε / 2) + ε / 2 = -1 + ε by ring] using hf N (by omega)
    change SignedAtomicDistance.distance P Qν ≤ _
    linarith only [htri, hactual, hreference, hsmall, hh]
  · intro hbias
    have hquant : q / N ≤ meanGap N L :=
      MeanBiasQuantization.critical_quantum_lower_bound (by omega) hL hband hbias
    have hpower : η⁻¹ * (N : ℝ) ^ (-5 / 4 : ℝ) ≤ (N : ℝ) ^ (-1 : ℝ) := by
      simpa only [show (-5 / 4 : ℝ) + 1 / 4 = -1 by ring] using he N (by omega)
    have hsmall : (N : ℝ) ^ (-5 / 4 : ℝ) ≤ η / N := by
      have hh := (inv_mul_le_iff₀ hη).mp hpower
      simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hh
    have herror : SignedAtomicDistance.distance P Qμ ≤ a * meanGap N L := by
      calc
        _ ≤ (N : ℝ) ^ (-5 / 4 : ℝ) := hactual
        _ ≤ η / N := hsmall
        _ = a * (q / N) := by dsimp [η]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hquant ha.le
    have hμM : μ ≤ 2 * (2 : ℝ) ^ C := (hm N (by omega) L hband).2
    have hνM : nominalMean N L ≤ 2 * (2 : ℝ) ^ C := by
      have hh := (FiniteChannelHierarchyBounds.nominal_bounds (by omega) hband).2
      have hp : (0 : ℝ) ≤ 2 ^ C := by positivity
      linarith only [hh, hp]
    exact QuadraticMeanLawComparison.finite_bounds P μ (nominalMean N L) (2 * (2 : ℝ) ^ C) α
      hμ hν hμM hνM hα herror

theorem article_17_3
    (C ε : ℝ) (hε : 0 < ε) :
    (∀ N L : ℕ, 2 ≤ N → 0 < L →
      countMoment (dyadicBlock N) L 1 - nominalMean N L =
        (2 ^ L : ℝ)⁻¹ * (MeanBiasQuantization.bias (dyadicBlock N) L : ℝ) ∧
      (countMoment (dyadicBlock N) L 1 = nominalMean N L ∨ (2 ^ L : ℝ)⁻¹ ≤ meanGap N L)) ∧
    (∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        nominalError N L ≤ (N : ℝ) ^ (-1 + ε) ∧
        (MeanBiasQuantization.bias (dyadicBlock N) L ≠ 0 →
          lowerConstant C * meanGap N L ≤ nominalError N L ∧
            nominalError N L ≤ (6 + lowerConstant C) * meanGap N L)) := by
  refine ⟨?_, uniform_comparison C ε hε⟩
  intro N L hN hL
  refine ⟨MeanBiasQuantization.main_17_3_integer_identity hN hL, ?_⟩
  simpa only [meanGap, nominalMean, dyadicBlock_card] using
    MeanBiasQuantization.finite_dichotomy hN hL (subset_refl (dyadicBlock N))

end PaperP1.OptimalNominalQuadratic
