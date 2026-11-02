module

public import PaperP1.Probability.QuadraticReferenceDistance
public import PaperP1.Asymptotics.ChannelMassPhaseEquivalent
public import PaperP1.Asymptotics.ExplicitReferenceAdmissibility
public import PaperP1.Arithmetic.HeightFiveChannelCorrection

/-! # Exact distance and uniform moving-phase equivalent of adjacent references

These are distances between constructed explicit references. No estimate
for their distances to the original run-count law is a premise or conclusion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AdjacentReferencePhase

open MeasureTheory PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent
  PaperP1.PoissonDifferenceSigned

def gap (N L h : ℕ) : ℝ := ∑' k : ℕ,
  |(QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) -
    QuadraticPoisson.reference (nominalMean N L) (coefficient N L (h + 1))) {k}|

def leadingGap (N L h : ℕ) : ℝ := phaseMass N L (h + 1) / 2 * norm (nominalMean N L) 2

theorem exact_gap (N L h : ℕ) (hh : 3 ≤ h + 1) :
    gap N L h = |heightMass N L (h + 1)| / 2 * norm (nominalMean N L) 2 := by
  rw [gap, QuadraticReferenceDistance.signed_distance _ _ _ (by unfold nominalMean; positivity),
    HeightFiveChannelCorrection.coefficient_succ N L h hh]
  have hid : coefficient N L h -
      (coefficient N L h + (nominalMean N L) ^ 2 / N * heightSum (h + 1) L) =
      -heightMass N L (h + 1) := by unfold heightMass; ring
  rw [hid, abs_neg]

theorem leadingGap_pos (N L h : ℕ) (hN : 0 < N) (hL : 0 < L) (hh : 3 ≤ h + 1) :
    0 < leadingGap N L h := by
  have hp := phaseMass_pos N L (h + 1) hN hL hh
  have hm : 0 ≤ nominalMean N L := by unfold nominalMean; positivity
  have hn := PoissonSecondDifferenceNorm.norm_second_lower_bound (nominalMean N L) hm
  have hnpos : 0 < norm (nominalMean N L) 2 := (by positivity : 0 < 2 * Real.exp (-(nominalMean N L))).trans_le hn
  exact mul_pos (div_pos hp (by norm_num)) hnpos

theorem uniform_relative (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < leadingGap N L h ∧ |gap N L h - leadingGap N L h| ≤ ε * leadingGap N L h := by
  obtain ⟨NP, hNP, hphase⟩ := ChannelMassPhaseEquivalent.uniform_relative C (h + 1) (by omega) ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max NP NG, by omega, ?_⟩
  intro N hN L hband
  have hNpos : 0 < N := by omega
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hp := phaseMass_pos N L (h + 1) hNpos hL (by omega)
  have hn : 0 ≤ norm (nominalMean N L) 2 := tsum_nonneg fun _ ↦ abs_nonneg _
  have hphaseabs : |(|heightMass N L (h + 1)| - phaseMass N L (h + 1))| ≤
      |heightMass N L (h + 1) - phaseMass N L (h + 1)| := by
    simpa only [abs_of_pos hp] using abs_abs_sub_abs_le_abs_sub
      (heightMass N L (h + 1)) (phaseMass N L (h + 1))
  refine ⟨leadingGap_pos N L h hNpos hL (by omega), ?_⟩
  rw [exact_gap N L h (by omega), leadingGap]
  calc
    _ = |(|heightMass N L (h + 1)| - phaseMass N L (h + 1))| *
        (norm (nominalMean N L) 2 / 2) := by
      rw [show |heightMass N L (h + 1)| / 2 * norm (nominalMean N L) 2 -
          phaseMass N L (h + 1) / 2 * norm (nominalMean N L) 2 =
          (|heightMass N L (h + 1)| - phaseMass N L (h + 1)) *
            (norm (nominalMean N L) 2 / 2) by ring,
        abs_mul, abs_of_nonneg (div_nonneg hn (by norm_num))]
    _ ≤ (ε * phaseMass N L (h + 1)) * (norm (nominalMean N L) 2 / 2) :=
      mul_le_mul_of_nonneg_right (hphaseabs.trans (hphase N (by omega) L hband)) (by positivity)
    _ = _ := by ring

theorem uniform_ratio (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < leadingGap N L h ∧ |gap N L h / leadingGap N L h - 1| ≤ ε := by
  obtain ⟨N₀, hN₀, hrelative⟩ := uniform_relative C h hh ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hp, he⟩ := hrelative N hN L hband
  refine ⟨hp, ?_⟩
  have hid : gap N L h / leadingGap N L h - 1 =
      (gap N L h - leadingGap N L h) / leadingGap N L h := by field_simp
  rw [hid, abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr he

theorem uniform_probability_gap (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ Q R : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) ∧
        (R : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference (nominalMean N L) (coefficient N L (h + 1)) ∧
        AtomicProbability.totalVariation Q R = gap N L h / 2 ∧
        0 < leadingGap N L h ∧ |AtomicProbability.totalVariation Q R / (leadingGap N L h / 2) - 1| ≤ ε := by
  obtain ⟨NG, hNG, hgap⟩ := uniform_ratio C h hh ε hε
  obtain ⟨NQ, hNQ, hprobQ⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  obtain ⟨NR, hNR, hprobR⟩ := ExplicitReferenceAdmissibility.uniform_probabilities C (h + 1) (by omega)
  refine ⟨max NG (max NQ NR), by omega, ?_⟩
  intro N hN L hband
  obtain ⟨Q, hQ⟩ := (hprobQ N (by omega) L hband).2.2.1
  obtain ⟨R, hR⟩ := (hprobR N (by omega) L hband).2.2.1
  obtain ⟨hp, he⟩ := hgap N (by omega) L hband
  have htv : AtomicProbability.totalVariation Q R = gap N L h / 2 := by
    have hs := AtomicProbabilityMetric.signed_distance Q R
    rw [hQ, hR] at hs
    change gap N L h = 2 * AtomicProbability.totalVariation Q R at hs
    linarith only [hs]
  refine ⟨Q, R, hQ, hR, htv, hp, ?_⟩
  rw [htv, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact he

end PaperP1.AdjacentReferencePhase
