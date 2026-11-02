module

public import PaperP1.Probability.CompletedLawShift
public import PaperP1.Probability.AtomicProbability
public import PaperP1.Probability.PoissonParameterStability

/-! # An actual Poisson probability law and its completed-l1 comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedPoissonMetric

open MeasureTheory PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson

def law (μ : ℝ) (hμ : 0 ≤ μ) : ProbabilityMeasure ℕ :=
  AtomicProbability.ofMass (PoissonSequence.mass μ)
    (fun k ↦ by unfold PoissonSequence.mass; positivity) (PoissonSequence.hasSum_mass μ hμ)

theorem realMass_law (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    AtomicProbability.realMass (law μ hμ) k = PoissonSequence.mass μ k :=
  AtomicProbability.ofMass_real_singleton _ _ _ k

theorem totalVariation_bound (ν : SignedLaw ℝ) (P : ProbabilityMeasure ℕ)
    (hP : ∀ k, AtomicProbability.realMass P k = ν.coeff k) (μ : ℝ) (hμ : 0 ≤ μ) :
    AtomicProbability.totalVariation P (law μ hμ) ≤ ‖ofFinite ν - poisson μ‖ / 2 := by
  have h := tsum_abs_coeff_le (ofFinite ν - poisson μ)
  simp only [map_sub, coeff_ofFinite, coeff_poisson] at h
  change (∑' k, |AtomicProbability.realMass P k - AtomicProbability.realMass (law μ hμ) k|) / 2 ≤ _
  simp_rw [hP, realMass_law]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem parameter_stability (μ ν : ℝ) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) :
    AtomicProbability.totalVariation (law μ hμ) (law ν hν) ≤ |μ - ν| := by
  have h := tsum_abs_coeff_le (poisson μ - poisson ν)
  simp only [map_sub, coeff_poisson] at h
  have hn := PoissonParameterStability.norm_difference hμ hν
  have ht : AtomicProbability.totalVariation (law μ hμ) (law ν hν) =
      (∑' k, |PoissonSequence.mass μ k - PoissonSequence.mass ν k|) / 2 := by
    change (∑' k, |AtomicProbability.realMass (law μ hμ) k - AtomicProbability.realMass (law ν hν) k|) / 2 = _
    simp only [realMass_law]
  rw [ht]
  linarith only [h, hn]

end PaperP1.CompletedPoissonMetric
