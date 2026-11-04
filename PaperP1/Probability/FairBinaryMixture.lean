module

public import PaperP1.Probability.BinaryForcingFlip

/-! # An arbitrary fair binary orientation gives the exact two-point mixture

The auxiliary law is an arbitrary finite probability, not necessarily
uniform. Fairness concerns the original uniform source word together
with independent auxiliary randomness.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FairBinaryMixture

open PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability PaperP1.UniformFubini

theorem pointwise (f : F₂ → ℝ) (z : F₂) :
    f z = f 0 + (f 1 - f 0) * PaperP1.BinaryForcingFlip.bitIndicator z := by
  have hz : z = 0 ∨ z = 1 := by revert z; decide
  rcases hz with rfl | rfl <;> norm_num [PaperP1.BinaryForcingFlip.bitIndicator]

theorem expectation_affine {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω)
    (f : Ω → ℝ) (c d : ℝ) :
    finiteExpectation P.weight (fun ω ↦ c + d * f ω) = c + d * finiteExpectation P.weight f := by
  rw [finiteExpectation_add, finiteExpectation_const, P.total_weight, one_mul,
    finiteExpectation_const_mul]

theorem nested {U Ξ : Type*} [Fintype U] [Nonempty U] [Fintype Ξ]
    (P : FiniteProbability Ξ) (g : U → Ξ → F₂)
    (hfair : average (fun u : U ↦ finiteExpectation P.weight
      (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) = (1 / 2 : ℝ))
    (f : F₂ → ℝ) :
    average (fun u : U ↦ finiteExpectation P.weight (fun ξ ↦ f (g u ξ))) = (f 0 + f 1) / 2 := by
  calc
    _ = average (fun u : U ↦ f 0 + (f 1 - f 0) * finiteExpectation P.weight
        (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) := by
      apply UniformFubini.congr
      intro u
      have he : (fun ξ ↦ f (g u ξ)) = fun ξ ↦
          f 0 + (f 1 - f 0) * PaperP1.BinaryForcingFlip.bitIndicator (g u ξ) :=
        funext fun ξ ↦ pointwise f (g u ξ)
      rw [he, expectation_affine]
    _ = f 0 + (f 1 - f 0) * average (fun u : U ↦ finiteExpectation P.weight
        (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g u ξ))) :=
      expectation_affine (uniformFiniteProbability U) _ _ _
    _ = (f 0 + f 1) / 2 := by rw [hfair]; ring

end PaperP1.FairBinaryMixture
