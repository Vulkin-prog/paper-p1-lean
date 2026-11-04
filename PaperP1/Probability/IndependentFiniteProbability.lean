module

public import PaperP1.Probability.UniformFubini

/-! # Independent finite laws and weighted Fubini

The auxiliary law may have arbitrary real weights. No uniformity or
nonempty-instance assumption on the auxiliary type is imposed separately
from its probability law.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentFiniteProbability

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.UniformFubini

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def product (P : FiniteProbability Ω) (Q : FiniteProbability Ξ) : FiniteProbability (Ω × Ξ) where
  weight := fun p ↦ P.weight p.1 * Q.weight p.2
  weight_nonneg := fun p ↦ mul_nonneg (P.weight_nonneg p.1) (Q.weight_nonneg p.2)
  total_weight := by
    simp only [Fintype.sum_prod_type, ← mul_sum, Q.total_weight, mul_one, P.total_weight]

theorem expectation_product (P : FiniteProbability Ω) (Q : FiniteProbability Ξ) (f : Ω × Ξ → ℝ) :
    finiteExpectation (product P Q).weight f =
      finiteExpectation P.weight (fun ω ↦ finiteExpectation Q.weight (fun ξ ↦ f (ω, ξ))) := by
  simp only [finiteExpectation, product, Fintype.sum_prod_type, mul_sum, mul_assoc]

theorem commute (P : FiniteProbability Ω) (Q : FiniteProbability Ξ) (f : Ω → Ξ → ℝ) :
    finiteExpectation P.weight (fun ω ↦ finiteExpectation Q.weight (fun ξ ↦ f ω ξ)) =
      finiteExpectation Q.weight (fun ξ ↦ finiteExpectation P.weight (fun ω ↦ f ω ξ)) := by
  simp only [finiteExpectation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ξ _
  apply sum_congr rfl
  intro ω _
  ring

theorem expectation_first (P : FiniteProbability Ω) (Q : FiniteProbability Ξ) (f : Ω → ℝ) :
    finiteExpectation (product P Q).weight (fun p ↦ f p.1) = finiteExpectation P.weight f := by
  rw [expectation_product]
  simp only [finiteExpectation_const, Q.total_weight, one_mul]

theorem expectation_second (P : FiniteProbability Ω) (Q : FiniteProbability Ξ) (f : Ξ → ℝ) :
    finiteExpectation (product P Q).weight (fun p ↦ f p.2) = finiteExpectation Q.weight f := by
  rw [expectation_product]
  change finiteExpectation P.weight (fun _ : Ω ↦ finiteExpectation Q.weight f) = finiteExpectation Q.weight f
  rw [finiteExpectation_const, P.total_weight, one_mul]

theorem uniform_commute [Nonempty Ω] (Q : FiniteProbability Ξ) (f : Ω → Ξ → ℝ) :
    average (fun ω ↦ finiteExpectation Q.weight (fun ξ ↦ f ω ξ)) =
      finiteExpectation Q.weight (fun ξ ↦ average (fun ω ↦ f ω ξ)) :=
  commute (uniformFiniteProbability Ω) Q f

end PaperP1.IndependentFiniteProbability
