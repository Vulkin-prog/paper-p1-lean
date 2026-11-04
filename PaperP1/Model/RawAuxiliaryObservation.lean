module

public import PaperP1.Model.RawWordObservation
public import PaperP1.Probability.IndependentFiniteProbability

/-! # Actual raw-word observations with arbitrary independent auxiliary randomness -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawAuxiliaryObservation

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem PaperP1.UniformFubini
  PaperP1.Algebra PaperP1.Probability PaperP1.IndependentFiniteProbability

variable {ι κ Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype Ξ]

theorem independent_words {M : ℕ} (v : ι → ℕ) (t : κ → ℕ)
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M v t))
    (P : FiniteProbability Ξ) (f : (ι → F₂) → Ξ → (κ → F₂) → ℝ) :
    finiteExpectation (product (cylinderProbability M) P).weight
      (fun p ↦ f (valueSystem M v p.1) p.2 (valueSystem M t p.1)) =
    finiteExpectation (product (uniformFiniteProbability (ι → F₂)) P).weight
      (fun p ↦ average (fun z : κ → F₂ ↦ f p.1 p.2 z)) := by
  rw [expectation_product, expectation_product]
  have h := PaperP1.RawWordObservation.independent_words v t hjoint
    (fun p ↦ finiteExpectation P.weight (fun ξ ↦ f p.1 ξ p.2))
  refine h.trans ?_
  apply UniformFubini.congr
  intro u
  exact uniform_commute P (fun z ξ ↦ f u ξ z)

end PaperP1.RawAuxiliaryObservation
