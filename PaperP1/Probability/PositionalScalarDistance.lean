module

public import PaperP1.Probability.PositionalCountProjection
public import PaperP1.Probability.PositionalBernoulliProducts
public import PaperP1.Probability.AtomicProbability

/-! # Actual scalar total variation is controlled by full-field distance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalScalarDistance

open Finset MeasureTheory PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection

variable {ι : Type*}

theorem bound (ν μ : Space ι) (P Q : ProbabilityMeasure ℕ)
    (hP : ∀ k, AtomicProbability.realMass P k = CompletedLaw.coeff k (projection ν))
    (hQ : ∀ k, AtomicProbability.realMass Q k = CompletedLaw.coeff k (projection μ)) :
    AtomicProbability.totalVariation P Q ≤ ‖ν - μ‖ / 2 := by
  have hs := CompletedLaw.tsum_abs_coeff_le (projection ν - projection μ)
  simp only [map_sub] at hs
  have hn := norm_projection_le (ν - μ)
  rw [map_sub] at hn
  change (∑' k, |AtomicProbability.realMass P k - AtomicProbability.realMass Q k|) / 2 ≤ _
  simp only [hP, hQ]
  exact div_le_div_of_nonneg_right (hs.trans hn) (by norm_num)

theorem poisson_projection (G : Finset ι) (p : ι → ℝ) :
    projection (PositionalBernoulliProducts.poisson G p) = CompletedPoisson.poisson (∑ x ∈ G, p x) := by
  rw [PositionalBernoulliProducts.poisson, projection_exp, map_sum]
  simp only [map_smul, projection_delta]
  rw [← sum_smul, CompletedPoisson.poisson]

end PaperP1.PositionalScalarDistance
