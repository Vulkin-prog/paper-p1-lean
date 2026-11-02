module

public import PaperP1.Asymptotics.ExplicitHermiteComparison
public import PaperP1.Asymptotics.ChannelMassPhaseLower

/-! # Reference-distance changes are negligible at the first omitted height

The conclusion is uniform for every actual target probability law. It does
not assume or assert an approximation of the original count by either law.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExplicitHermitePhaseStability

open MeasureTheory PaperP1.FiniteChannelHierarchy PaperP1.ChannelMassPhaseEquivalent

theorem uniform_stability (C : ℝ) (h : ℕ) (hh : 3 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∃ Q H : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure =
          QuadraticPoisson.reference (nominalMean N L) (coefficient N L h) ∧
        (H : Measure ℕ).toSignedMeasure = CompletedLaw.toSignedMeasure
          (HermiteReference.reference (nominalMean N L) (coefficient N L h)) ∧
        0 < phaseMass N L (h + 1) ∧ ∀ P : ProbabilityMeasure ℕ,
          |AtomicProbability.totalVariation P Q - AtomicProbability.totalVariation P H| ≤
            ε * phaseMass N L (h + 1) := by
  obtain ⟨NR, hNR, href⟩ := ExplicitHermiteComparison.uniform_reference_stability C h hh (1 / 12) (by norm_num)
  obtain ⟨d, hd, ND, hND, hlower⟩ := ChannelMassPhaseLower.uniform_coarse_lower C (h + 1) (by omega)
  have hprod : 0 < ε * d := mul_pos hε hd
  obtain ⟨NF, hfactor⟩ := HalfCountSchedule.factor_absorption (1 / (ε * d)) (-5 / 4) (1 / 4) (by norm_num)
  refine ⟨max NR (max ND NF), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨Q, H, hQ, hH, hdist⟩ := href N (by omega) L hband
  have hl := hlower N (by omega) L hband
  have hp : 0 < phaseMass N L (h + 1) := (div_pos hd hn).trans_le hl
  refine ⟨Q, H, hQ, hH, hp, ?_⟩
  intro P
  have hr := hdist P
  norm_num only [show (-4 / 3 : ℝ) + 1 / 12 = -5 / 4 by ring] at hr
  have hf := hfactor N (by omega)
  norm_num only [show (-5 / 4 : ℝ) + 1 / 4 = -1 by ring] at hf
  have hbudget : (N : ℝ) ^ (-5 / 4 : ℝ) ≤ (ε * d) * (N : ℝ) ^ (-(1 : ℝ)) := by
    have hs := mul_le_mul_of_nonneg_left hf hprod.le
    rw [← mul_assoc, mul_one_div_cancel hprod.ne', one_mul] at hs
    simpa only [neg_div] using hs
  calc
    _ ≤ (N : ℝ) ^ (-5 / 4 : ℝ) / 2 := by simpa only [neg_div] using hr
    _ ≤ (N : ℝ) ^ (-5 / 4 : ℝ) := by nlinarith only [Real.rpow_nonneg hn.le (-5 / 4 : ℝ)]
    _ ≤ (ε * d) * (N : ℝ) ^ (-(1 : ℝ)) := hbudget
    _ = ε * (d / N) := by rw [Real.rpow_neg_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl hε.le

end PaperP1.ExplicitHermitePhaseStability
