module

public import PaperP1.Probability.CompletedLawShift
public import PaperP1.Probability.PoissonSecondDifferenceNorm
public import PaperP1.Probability.AtomicProbabilityMetric

/-! # Exact ordinary distance between quadratic references at the same mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticReferenceDistance

open MeasureTheory PaperP1.CompletedLaw PaperP1.CompletedLawShift
  PaperP1.PoissonSequence PaperP1.PoissonDifferenceSigned

theorem singleton_difference (μ α β : ℝ) (k : ℕ) :
    (QuadraticPoisson.reference μ α - QuadraticPoisson.reference μ β) {k} =
      ((α - β) / 2) * secondDifference (mass μ) k := by
  rw [← quadratic_actual_signed_measure μ α, ← quadratic_actual_signed_measure μ β,
    _root_.sub_apply, toSignedMeasure_singleton, toSignedMeasure_singleton,
    coeff_quadratic, coeff_quadratic]
  unfold quadraticMass
  ring

theorem signed_distance (μ α β : ℝ) (hμ : 0 ≤ μ) :
    (∑' k : ℕ, |(QuadraticPoisson.reference μ α - QuadraticPoisson.reference μ β) {k}|) =
      (|α - β| / 2) * norm μ 2 := by
  simp_rw [singleton_difference, abs_mul]
  rw [tsum_mul_left, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    norm_eq_l1 μ hμ 2, PoissonSecondDifferenceNorm.difference_two_eq_secondDifference]
  rfl

theorem totalVariation_exact (μ α β : ℝ) (hμ : 0 ≤ μ) (Q R : ProbabilityMeasure ℕ)
    (hQ : (Q : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference μ α)
    (hR : (R : Measure ℕ).toSignedMeasure = QuadraticPoisson.reference μ β) :
    AtomicProbability.totalVariation Q R = (|α - β| / 4) * norm μ 2 := by
  have h := AtomicProbabilityMetric.signed_distance Q R
  rw [hQ, hR, signed_distance μ α β hμ] at h
  linarith only [h]

end PaperP1.QuadraticReferenceDistance
