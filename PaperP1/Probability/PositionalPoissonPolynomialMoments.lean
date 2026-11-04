module

public import PaperP1.Probability.PositionalReferenceMoments
public import PaperP1.Probability.PositionalPoissonObservables

/-! # All fixed total-count moments of a bounded independent Poisson field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonPolynomialMoments

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalCountProjection

variable {ι : Type*}

theorem empty_pair_target (G : Finset ι) (p : ι → ℝ) :
    PositionalCompoundPoisson.target G ∅ p (fun _ ↦ 0) = PositionalBernoulliProducts.poisson G p := by
  simp only [PositionalCompoundPoisson.target, PositionalCompoundPoisson.incidence, sum_empty,
    sub_zero, prod_empty, mul_one]
  exact (PositionalPoissonObservables.poisson_product G p).symm

theorem uniform_bound (M : ℝ) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (G : Finset ι) (p : ι → ℝ),
      (∀ x ∈ G, 0 ≤ p x) → (∑ x ∈ G, p x) ≤ M →
      Summable (fun v ↦ coeff v (PositionalBernoulliProducts.poisson G p) *
        (1 + (totalCount v : ℝ)) ^ r) ∧
      (∑' v, coeff v (PositionalBernoulliProducts.poisson G p) *
        (1 + (totalCount v : ℝ)) ^ r) ≤ B := by
  obtain ⟨B, hB, h⟩ := PositionalReferenceMoments.uniform_bound (ι := ι) M r
  refine ⟨B, hB, ?_⟩
  intro G p hp hmean
  have hsite : ∀ x ∈ G, 0 ≤ p x - PositionalCompoundPoisson.incidence ∅ (fun _ ↦ 0) x := by
    simpa only [PositionalCompoundPoisson.incidence, sum_empty, sub_zero] using hp
  have hh := h G ∅ p (fun _ ↦ 0) (by simp) hsite (by simp) hmean
  simpa only [empty_pair_target] using hh

end PaperP1.PositionalPoissonPolynomialMoments
