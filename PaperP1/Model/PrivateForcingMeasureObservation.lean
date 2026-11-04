module

public import PaperP1.Model.RandomizedPrivateForcingClass
public import PaperP1.Probability.FiniteOrientationObservation

/-! # Exact finite observation of an arbitrary private forcing and its orientation

The observation also records every prime output at sources outside Good.
The observed map is completed canonically on Good at tables of zero mass,
so the universal finite-law theorem applies pointwise on the entire table
space. At every actual auxiliary sample its prime output is unchanged.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateForcingMeasureObservation

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Probability PaperP1.Algebra
  PaperP1.RandomizedHybridField PaperP1.IndependentFiniteProbability

local instance privateMeasureObservationDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Index (M K : ℕ) (G : Finset ℕ) :=
  (G × (Fin (K + 1) → F₂)) ⊕ (G × SampleSpace M × PrimeUpTo M)

abbrev Observation (M K : ℕ) (G : Finset ℕ) :=
  PaperP1.FiniteOrientationObservation.Table (Index M K G) Unit

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}

def observedOrientation (j : G) (u : Fin (K + 1) → F₂) (t : Observation M K G) : F₂ :=
  t.value (Sum.inl (j, u)) Unit.unit

def observedForce (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (j : G) (p : SampleSpace M × Observation M K G) : SampleSpace M × Observation M K G :=
  if j.val ∈ Good then (primeForce D b observedOrientation j p.1 p.2, p.2)
  else ((fun r ↦ p.2.value (Sum.inr (j, p.1, r)) Unit.unit), p.2)

theorem observed_agrees (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂) :
    PaperP1.RandomizedPrivateForcingClass.AgreesOnGood D b observedOrientation (observedForce D b) := by
  intro j hj p
  rw [observedForce, ite_eq_left hj]

variable {Ξ : Type*} [MeasurableSpace Ξ]

def decisions (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (F : G → SampleSpace M → Ξ → SampleSpace M) (i : Index M K G) (_u : Unit) (ξ : Ξ) : F₂ :=
  match i with
  | Sum.inl (j, u) => g j u ξ
  | Sum.inr (j, ω, r) => F j ω ξ r

def encode (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (F : G → SampleSpace M → Ξ → SampleSpace M) : Ξ → Observation M K G :=
  PaperP1.FiniteOrientationObservation.encode (decisions g F)

theorem encode_measurable (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (F : G → SampleSpace M → Ξ → SampleSpace M)
    (hg : ∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s})
    (hF : ∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r = s}) : Measurable (encode g F) := by
  apply PaperP1.FiniteOrientationObservation.encode_measurable
  intro i _u s
  cases i with
  | inl a => exact hg a.1 a.2 s
  | inr a => exact hF a.1 a.2.1 a.2.2 s

def law (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M → Ξ → SampleSpace M)
    (h : Measurable (encode g F)) : FiniteProbability (Observation M K G) :=
  finiteObservationProbability μ (encode g F) h

omit [MeasurableSpace Ξ] in
theorem agrees_of_prescription (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M → Ξ → SampleSpace M)
    (hhit : ∀ j : G, j.val ∈ Good → ∀ ω ξ,
      PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) (F j ω ξ) =
        PaperP1.RandomizedPrivatePalmForcing.orientedWord b
          (g j (PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) ξ))
    (hout : ∀ j : G, ∀ hj : j.val ∈ Good, ∀ ω ξ, ∀ r : PrimeUpTo M,
      (∀ i, r ≠ fullPivots D j hj i) → F j ω ξ r = ω r) :
    ∀ j : G, j.val ∈ Good → ∀ ω ξ, F j ω ξ = primeForce D b g j ω ξ := by
  intro j hj ω ξ
  rw [primeForce_good D b g j hj]
  exact PaperP1.PrivatePrimeForcingUniqueness.randomized_unique
    (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) (full_basis D j hj) b (g j)
    (F j) (hhit j hj) (hout j hj) ω ξ

omit [MeasurableSpace Ξ] in
theorem primeForce_encode (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M → Ξ → SampleSpace M)
    (j : G) (ω : SampleSpace M) (ξ : Ξ) :
    primeForce D b observedOrientation j ω (encode g F ξ) = primeForce D b g j ω ξ := rfl

omit [MeasurableSpace Ξ] in
theorem prime_output_encode (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M → Ξ → SampleSpace M)
    (hF : ∀ j : G, j.val ∈ Good → ∀ ω ξ, F j ω ξ = primeForce D b g j ω ξ)
    (j : G) (ω : SampleSpace M) (ξ : Ξ) :
    (observedForce D b j (ω, encode g F ξ)).1 = F j ω ξ := by
  by_cases hj : j.val ∈ Good
  · rw [observedForce, ite_eq_left hj]
    change primeForce D b observedOrientation j ω (encode g F ξ) = _
    rw [primeForce_encode]
    exact (hF j hj ω ξ).symm
  · rw [observedForce, ite_eq_right hj]
    rfl

theorem prime_observable_expectation (D : Data M Y K G Good anchor)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M → Ξ → SampleSpace M)
    (h : Measurable (encode g F))
    (hF : ∀ j : G, j.val ∈ Good → ∀ ω ξ, F j ω ξ = primeForce D b g j ω ξ)
    (j : G) (f : SampleSpace M → SampleSpace M → ℝ) :
    finiteExpectation (PaperP1.RandomizedHybridField.law (M := M) (law μ g F h)).weight
      (fun p ↦ f p.1 (observedForce D b j p).1) =
      PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦ ∫ ξ, f ω (F j ω ξ) ∂μ) := by
  rw [PaperP1.RandomizedHybridField.law, expectation_product]
  change PaperP1.UniformFubini.average _ = _
  apply PaperP1.UniformFubini.congr
  intro ω
  have he := finiteObservation_expectation μ (encode g F) h
    (fun t ↦ f ω (observedForce D b j (ω, t)).1)
  simpa only [law, prime_output_encode D b g F hF] using he

def offsite (μ : Measure Ξ) (b : Fin (K + 1) → F₂)
    (F : G → SampleSpace M → Ξ → SampleSpace M) : ℝ :=
  ∑ j : G, PaperP1.AnchoredPrivateField.rate K * PaperP1.UniformFubini.average (fun ω : SampleSpace M ↦
    ∫ ξ, ∑ k ∈ (univ : Finset G).erase j,
      |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω) : ℝ) -
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k (F j ω ξ))| ∂μ)

theorem offsite_observation (D : Data M Y K G Good anchor)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M → Ξ → SampleSpace M)
    (h : Measurable (encode g F))
    (hF : ∀ j : G, j.val ∈ Good → ∀ ω ξ, F j ω ξ = primeForce D b g j ω ξ) :
    PaperP1.PositiveForcingCostLower.offsite univ
      (PaperP1.RandomizedHybridField.law (M := M) (law μ g F h)) (indicator b) (observedForce D b) =
        offsite μ b F := by
  unfold PaperP1.PositiveForcingCostLower.offsite offsite
  apply sum_congr rfl
  intro j _hj
  rw [indicator_marginal D]
  congr 1
  change finiteExpectation (PaperP1.RandomizedHybridField.law (M := M) (law μ g F h)).weight
    (fun p ↦ ∑ k ∈ (univ : Finset G).erase j,
      |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k p.1) : ℝ) -
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k (observedForce D b j p).1)|) = _
  exact prime_observable_expectation D μ b g F h hF j (fun ω ω' ↦
    ∑ k ∈ (univ : Finset G).erase j,
      |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω) : ℝ) -
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω')|)

end PaperP1.PrivateForcingMeasureObservation
