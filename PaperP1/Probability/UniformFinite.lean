module

public import PaperP1.Probability.Convolution

/-!
# Actual expectations for the uniform finite probability law

These identities connect the constructed normalized real weights to ordinary
cardinality ratios. No independence assumption is needed.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem uniformFiniteExpectation_eq (X : Ω → ℝ) :
    finiteExpectation (uniformFiniteProbability Ω).weight X =
      (∑ ω, X ω) / Fintype.card Ω := by
  change (∑ ω, (Fintype.card Ω : ℝ)⁻¹ * X ω) = _
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem uniformFiniteExpectation_indicator (E : Ω → Prop) [DecidablePred E] :
    finiteExpectation (uniformFiniteProbability Ω).weight
        (fun ω => if E ω then (1 : ℝ) else 0) =
      ((Finset.univ.filter E).card : ℝ) / Fintype.card Ω := by
  rw [uniformFiniteExpectation_eq]
  simp

end PaperP1.Probability
