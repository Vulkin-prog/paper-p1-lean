module

public import PaperP1.Model.AnchoredPrivateField
public import PaperP1.Model.RandomizedPrivatePalmForcing
public import PaperP1.Probability.IndependentFiniteProbability

/-! # A valid randomized field on the entire original retained population

Fully private good sources use the prescribed fair randomized orientation.
Other retained sources use the compatible anchor-preserving map. The
prime/auxiliary product sample is explicit. Conditional laws are proved
for all observables of the ORIGINAL prime sample; the auxiliary output
is not asserted independent of the forced sample.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedHybridField

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.Probability PaperP1.Algebra PaperP1.UniformFubini PaperP1.PrivatePivotGeometry
  PaperP1.IndependentFiniteProbability

local instance randomizedHybridDecidable (P : Prop) : Decidable P := Classical.propDecidable P

structure Data (M Y K : ℕ) (G Good : Finset ℕ) (anchor : G → Fin (K + 1)) : Prop where
  anchored : PaperP1.AnchoredPrivateField.Data M Y K G anchor
  good : ∀ j : G, j.val ∈ Good → ∀ i : Fin (K + 1), Y < PaperP1.OddPrimePivot.largestOddPrime (j.val + i.val)

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}

def fullPivots (D : Data M Y K G Good anchor) (j : G) (hj : j.val ∈ Good) :
    Fin (K + 1) → PrimeUpTo M :=
  cylinderPivot (D.anchored.window j).boundary_pos (D.anchored.window j).cutoff
    (fun i ↦ (D.anchored.window j).small_pos.trans_lt (D.good j hj i))

theorem full_basis (D : Data M Y K G Good anchor) (j : G) (hj : j.val ∈ Good) (i : Fin (K + 1)) :
    valueSystem M (fun k : Fin (K + 1) ↦ j.val + k.val) (Pi.single (fullPivots D j hj i) 1) = Pi.single i 1 := by
  apply cylinderPivot_basis
  intro k
  exact (D.anchored.window j).word_width.trans (D.good j hj k).le

variable {Ξ : Type*}

def primeForce (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (j : G) (ω : SampleSpace M) (ξ : Ξ) : SampleSpace M :=
  if hj : j.val ∈ Good then
    PaperP1.RandomizedPrivatePalmForcing.force (fun i : Fin (K + 1) ↦ j.val + i.val)
      (fullPivots D j hj) b (g j) ω ξ
  else PaperP1.AnchoredPrivateField.force D.anchored b j ω

def force (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (j : G) (p : SampleSpace M × Ξ) : SampleSpace M × Ξ :=
  (primeForce D b g j p.1 p.2, p.2)

def indicator (b : Fin (K + 1) → F₂) (j : G) (p : SampleSpace M × Ξ) : Bool :=
  PaperP1.AnchoredPrivateField.indicator b j p.1

theorem primeForce_good (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (j : G) (hj : j.val ∈ Good)
    (ω : SampleSpace M) (ξ : Ξ) :
    primeForce D b g j ω ξ = PaperP1.RandomizedPrivatePalmForcing.force
      (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) b (g j) ω ξ := by
  rw [primeForce, dite_eq_left hj]

theorem primeForce_other (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (j : G) (hj : j.val ∉ Good)
    (ω : SampleSpace M) (ξ : Ξ) :
    primeForce D b g j ω ξ = PaperP1.AnchoredPrivateField.force D.anchored b j ω := by
  rw [primeForce, dite_eq_right hj]

theorem force_hits (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (j : G) (p : SampleSpace M × Ξ) :
    indicator b j (force D b g j p) = true := by
  change PaperP1.AnchoredPrivateField.indicator b j (primeForce D b g j p.1 p.2) = true
  by_cases hj : j.val ∈ Good
  · rw [primeForce_good D b g j hj]
    exact decide_eq_true (PaperP1.RandomizedPrivatePalmForcing.hits
      (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) (full_basis D j hj) b (g j) p.1 p.2)
  · rw [primeForce_other D b g j hj]
    exact PaperP1.AnchoredPrivateField.force_hits D.anchored b j p.1

theorem restricted_indicator (b : Fin (K + 1) → F₂) (j : G) (f : SampleSpace M → ℝ) :
    average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b
      (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) then f ω else 0) =
      average (fun ω : SampleSpace M ↦ PaperP1.Probability.indicatorValue
        (PaperP1.AnchoredPrivateField.indicator b j ω) * f ω) := by
  apply UniformFubini.congr
  intro ω
  rw [PaperP1.AnchoredPrivateField.indicator_value]
  by_cases h : PaperP1.BinaryForcingFlip.orbit b (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω)
  · rw [ite_eq_left h, ite_eq_left h, one_mul]
  · rw [ite_eq_right h, ite_eq_right h, zero_mul]

variable [Fintype Ξ]

def law (P : FiniteProbability Ξ) : FiniteProbability (SampleSpace M × Ξ) :=
  product (cylinderProbability M) P

theorem indicator_marginal (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (j : G) :
    exactMarginal (law (M := M) P) (indicator b) j = PaperP1.AnchoredPrivateField.rate K := by
  change finiteExpectation (product (cylinderProbability M) P).weight
    (fun p ↦ indicatorValue (PaperP1.AnchoredPrivateField.indicator b j p.1)) = _
  exact (expectation_first (cylinderProbability M) P
    (fun ω : SampleSpace M ↦ indicatorValue (PaperP1.AnchoredPrivateField.indicator b j ω))).trans
      (PaperP1.AnchoredPrivateField.indicator_marginal D.anchored b j)

theorem weighted_prime_palm (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hfair : ∀ j : G, j.val ∈ Good → average (fun u : Fin (K + 1) → F₂ ↦
      finiteExpectation P.weight (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g j u ξ))) = (1 / 2 : ℝ))
    (j : G) (f : SampleSpace M → ℝ) :
    PaperP1.AnchoredPrivateField.rate K * finiteExpectation (law (M := M) P).weight
      (fun p ↦ f (primeForce D b g j p.1 p.2)) =
      average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b
        (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) then f ω else 0) := by
  rw [law, expectation_product]
  by_cases hj : j.val ∈ Good
  · simp_rw [primeForce_good D b g j hj]
    simpa only [Fintype.card_fin, Nat.add_sub_cancel, PaperP1.AnchoredPrivateField.rate,
      cylinderProbability, average] using
      PaperP1.RandomizedPrivatePalmForcing.weighted_conditional
        (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) (full_basis D j hj)
        b P (g j) (hfair j hj) f
  · simp_rw [primeForce_other D b g j hj]
    have he (ω : SampleSpace M) : finiteExpectation P.weight
        (fun _ : Ξ ↦ f (PaperP1.AnchoredPrivateField.force D.anchored b j ω)) =
          f (PaperP1.AnchoredPrivateField.force D.anchored b j ω) := by
      rw [finiteExpectation_const, P.total_weight, one_mul]
    simp_rw [he]
    have h := PaperP1.AnchoredPrivateField.weighted_palm D.anchored b j f
    rw [PaperP1.AnchoredPrivateField.indicator_marginal D.anchored] at h
    exact h.trans (restricted_indicator b j f).symm

theorem prime_conditional (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hfair : ∀ j : G, j.val ∈ Good → average (fun u : Fin (K + 1) → F₂ ↦
      finiteExpectation P.weight (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g j u ξ))) = (1 / 2 : ℝ))
    (j : G) (f : SampleSpace M → ℝ) :
    finiteExpectation (law (M := M) P).weight (fun p ↦ f ((force D b g j p).1)) =
      average (fun ω : SampleSpace M ↦ if PaperP1.BinaryForcingFlip.orbit b
        (valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) ω) then f ω else 0) /
          PaperP1.AnchoredPrivateField.rate K := by
  apply (eq_div_iff (PaperP1.AnchoredPrivateField.rate_pos K).ne').mpr
  simpa only [force, mul_comm] using weighted_prime_palm D P b g hfair j f

theorem weighted_indicator_palm (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (hfair : ∀ j : G, j.val ∈ Good → average (fun u : Fin (K + 1) → F₂ ↦
      finiteExpectation P.weight (fun ξ ↦ PaperP1.BinaryForcingFlip.bitIndicator (g j u ξ))) = (1 / 2 : ℝ))
    (j k : G) :
    exactMarginal (law (M := M) P) (indicator b) j * finiteExpectation (law (M := M) P).weight
      (fun p ↦ indicatorValue (indicator b k (force D b g j p))) =
      finiteExpectation (law (M := M) P).weight (fun p ↦
        indicatorValue (indicator b j p) * indicatorValue (indicator b k p)) := by
  rw [indicator_marginal D]
  change PaperP1.AnchoredPrivateField.rate K * finiteExpectation (law (M := M) P).weight
      (fun p ↦ indicatorValue (PaperP1.AnchoredPrivateField.indicator b k (primeForce D b g j p.1 p.2))) =
    finiteExpectation (law (M := M) P).weight (fun p ↦
      indicatorValue (PaperP1.AnchoredPrivateField.indicator b j p.1) *
        indicatorValue (PaperP1.AnchoredPrivateField.indicator b k p.1))
  have h := weighted_prime_palm D P b g hfair j
    (fun ω : SampleSpace M ↦ indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω))
  rw [restricted_indicator] at h
  exact h.trans (expectation_first (cylinderProbability M) P
    (fun ω : SampleSpace M ↦ indicatorValue (PaperP1.AnchoredPrivateField.indicator b j ω) *
      indicatorValue (PaperP1.AnchoredPrivateField.indicator b k ω))).symm

theorem total_marginal (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) :
    (∑ j : G, exactMarginal (law (M := M) P) (indicator b) j) =
      G.card * PaperP1.AnchoredPrivateField.rate K := by
  simp only [indicator_marginal D, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]

def cost (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) : ℝ :=
  PaperP1.ForcingCoordinateCost.cost univ (law (M := M) P) (indicator b) (force D b g)

def offsite (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) : ℝ :=
  PaperP1.PositiveForcingCostLower.offsite univ (law (M := M) P) (indicator b) (force D b g)

theorem cost_diagonal_decomposition (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) :
    cost D P b g = G.card * (PaperP1.AnchoredPrivateField.rate K) ^ 2 + offsite D P b g := by
  have h := PaperP1.ForcingCoordinateCost.exact_diagonal_decomposition univ (law (M := M) P)
    (indicator b) (force D b g) (fun j _ p ↦ force_hits D b g j p)
  simpa only [cost, offsite, PaperP1.PositiveForcingCostLower.offsite, indicator_marginal D,
    sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using h

end PaperP1.RandomizedHybridField
