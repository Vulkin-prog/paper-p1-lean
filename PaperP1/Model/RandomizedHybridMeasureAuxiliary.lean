module

public import PaperP1.Model.RandomizedHybridField
public import PaperP1.Probability.FiniteOrientationObservation

/-! # Actual hybrid costs and Palm identities with arbitrary auxiliary measures

Only the finite table of all source-word orientation decisions is observed.
Its exact pushforward law preserves both the actual prime forcing and each
real expectation. Integrals below use the independent auxiliary law with
the original uniform prime sample outside it.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedHybridMeasureAuxiliary

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Probability
  PaperP1.Algebra PaperP1.UniformFubini PaperP1.RandomizedHybridField
  PaperP1.IndependentFiniteProbability

local instance measureAuxiliaryDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}
variable {Ξ : Type*} [MeasurableSpace Ξ]

def observedOrientation (j : G) (u : Fin (K + 1) → F₂)
    (t : PaperP1.FiniteOrientationObservation.Table G (Fin (K + 1) → F₂)) : F₂ := t.value j u

omit [MeasurableSpace Ξ] in
theorem primeForce_encode (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (j : G) (ω : SampleSpace M) (ξ : Ξ) :
    primeForce D b observedOrientation j ω (PaperP1.FiniteOrientationObservation.encode g ξ) =
      primeForce D b g j ω ξ := rfl

theorem prime_observable_expectation (D : Data M Y K G Good anchor)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hg : Measurable (PaperP1.FiniteOrientationObservation.encode g))
    (j : G) (f : SampleSpace M → SampleSpace M → ℝ) :
    finiteExpectation (law (M := M) (PaperP1.FiniteOrientationObservation.law μ g hg)).weight
      (fun p ↦ f p.1 (primeForce D b observedOrientation j p.1 p.2)) =
      PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦ ∫ ξ, f ω (primeForce D b g j ω ξ) ∂μ) := by
  rw [law, expectation_product]
  change PaperP1.UniformFubini.average _ = _
  apply UniformFubini.congr
  intro ω
  exact PaperP1.FiniteOrientationObservation.expectation_eq μ g hg
    (fun t ↦ f ω (primeForce D b observedOrientation j ω t))

theorem fairness_eq (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hg : Measurable (PaperP1.FiniteOrientationObservation.encode g)) (j : G) :
    PaperP1.UniformFubini.average (fun u : Fin (K + 1) → F₂ ↦
      finiteExpectation (PaperP1.FiniteOrientationObservation.law μ g hg).weight
        (fun t ↦ PaperP1.BinaryForcingFlip.bitIndicator (observedOrientation j u t))) =
      PaperP1.UniformFubini.average (fun u : Fin (K + 1) → F₂ ↦ ∫ ξ, PaperP1.BinaryForcingFlip.bitIndicator (g j u ξ) ∂μ) := by
  apply UniformFubini.congr
  intro u
  exact PaperP1.FiniteOrientationObservation.coordinate_expectation μ g hg j u
    PaperP1.BinaryForcingFlip.bitIndicator

theorem weighted_prime_palm (D : Data M Y K G Good anchor)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hg : Measurable (PaperP1.FiniteOrientationObservation.encode g))
    (hfair : ∀ j : G, j.val ∈ Good → PaperP1.UniformFubini.average (fun u : Fin (K + 1) → F₂ ↦
      ∫ ξ, PaperP1.BinaryForcingFlip.bitIndicator (g j u ξ) ∂μ) = (1 / 2 : ℝ))
    (j : G) (f : SampleSpace M → ℝ) :
    PaperP1.AnchoredPrivateField.rate K *
      PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦ ∫ ξ, f (primeForce D b g j ω ξ) ∂μ) =
      PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b
        (PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω)
        then f ω else 0) := by
  have hf : ∀ j : G, j.val ∈ Good → PaperP1.UniformFubini.average (fun u : Fin (K + 1) → F₂ ↦
      finiteExpectation (PaperP1.FiniteOrientationObservation.law μ g hg).weight
        (fun t ↦ PaperP1.BinaryForcingFlip.bitIndicator (observedOrientation j u t))) = (1 / 2 : ℝ) := by
    intro k hk
    rw [fairness_eq μ g hg k]
    exact hfair k hk
  have h := PaperP1.RandomizedHybridField.weighted_prime_palm D
    (PaperP1.FiniteOrientationObservation.law μ g hg) b observedOrientation hf j f
  rw [prime_observable_expectation D μ b g hg j (fun _ ω' ↦ f ω')] at h
  exact h

theorem prime_conditional (D : Data M Y K G Good anchor)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hg : Measurable (PaperP1.FiniteOrientationObservation.encode g))
    (hfair : ∀ j : G, j.val ∈ Good → PaperP1.UniformFubini.average (fun u : Fin (K + 1) → F₂ ↦
      ∫ ξ, PaperP1.BinaryForcingFlip.bitIndicator (g j u ξ) ∂μ) = (1 / 2 : ℝ))
    (j : G) (f : SampleSpace M → ℝ) :
    PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦ ∫ ξ, f (primeForce D b g j ω ξ) ∂μ) =
      PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b
        (PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω)
        then f ω else 0) / PaperP1.AnchoredPrivateField.rate K := by
  apply (eq_div_iff (PaperP1.AnchoredPrivateField.rate_pos K).ne').mpr
  simpa only [mul_comm] using weighted_prime_palm D μ b g hg hfair j f

def offsite (D : Data M Y K G Good anchor) (μ : Measure Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) : ℝ :=
  ∑ j : G, PaperP1.AnchoredPrivateField.rate K * PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦
    ∫ ξ, ∑ k ∈ (univ : Finset G).erase j,
      |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω) : ℝ) -
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k (primeForce D b g j ω ξ))| ∂μ)

theorem offsite_observation (D : Data M Y K G Good anchor)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hg : Measurable (PaperP1.FiniteOrientationObservation.encode g)) :
    PaperP1.RandomizedHybridField.offsite D (PaperP1.FiniteOrientationObservation.law μ g hg)
      b observedOrientation = offsite D μ b g := by
  unfold PaperP1.RandomizedHybridField.offsite PaperP1.PositiveForcingCostLower.offsite offsite
  apply sum_congr rfl
  intro j _hj
  rw [indicator_marginal D]
  congr 1
  change finiteExpectation (law (M := M) (PaperP1.FiniteOrientationObservation.law μ g hg)).weight
    (fun p ↦ ∑ k ∈ (univ : Finset G).erase j,
      |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k p.1) : ℝ) -
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k
          (primeForce D b observedOrientation j p.1 p.2))|) = _
  exact prime_observable_expectation D μ b g hg j (fun ω ω' ↦
    ∑ k ∈ (univ : Finset G).erase j,
      |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω) : ℝ) -
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω')|)

end PaperP1.RandomizedHybridMeasureAuxiliary
