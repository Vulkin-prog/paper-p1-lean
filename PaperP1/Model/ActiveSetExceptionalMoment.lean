module

public import PaperP1.Model.ActiveSetCylinder
public import PaperP1.Model.RetainedMomentTransfer
public import PaperP1.Probability.ExceptionalEventHolder

/-! # The contribution of any polynomially bounded active-set observable on the actual exceptional event -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveSetExceptionalMoment

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.RetainedActiveCount
  PaperP1.MaximumDirectActive PaperP1.CountObservables

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def value (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∫ ω, if ¬RetainedGoodEdges.Retained H N L (activeSet G L ω) then f (activeSet G L ω) else 0 ∂infiniteRademacherMeasure

theorem finite_value (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : Finset ℕ → ℝ) :
    value H N L G f = finiteExpectation (cylinderProbability (cutoff G L)).weight
      (fun σ ↦ if ¬RetainedGoodEdges.Retained H N L (activeSites G (fun x ↦ startIndicator x L) σ) then
        f (activeSites G (fun x ↦ startIndicator x L) σ) else 0) := by
  exact ActiveSetCylinder.observable_integral G L
    (fun A ↦ if ¬RetainedGoodEdges.Retained H N L A then f A else 0)

theorem eighth_bound (H : ℝ) (N L : ℕ) (G : Finset ℕ) (f : Finset ℕ → ℝ) (j : ℕ)
    (hbound : ∀ A ⊆ G, 0 ≤ f A ∧ f A ≤ (A.card : ℝ) ^ j) :
    value H N L G f ≤ countMoment G L (8 * j) ^ (1 / 8 : ℝ) *
      RetainedCountCylinder.badProbability H N L G ^ (7 / 8 : ℝ) := by
  let M := cutoff G L
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  let X := fun σ : SampleSpace M ↦ f (activeSites G J σ)
  let B := fun σ : SampleSpace M ↦ ¬RetainedGoodEdges.Retained H N L (activeSites G J σ)
  have hX (σ : SampleSpace M) : 0 ≤ X σ := (hbound _ (filter_subset _ _)).1
  have hmoment : finiteExpectation (cylinderProbability M).weight (fun σ ↦ X σ ^ 8) ≤ countMoment G L (8 * j) := by
    rw [countMoment, RetainedMomentTransfer.original_observable_integral G L (fun n ↦ (n : ℝ) ^ (8 * j))]
    apply finiteExpectation_mono (cylinderProbability M)
    intro σ
    have hboundX : X σ ≤ (indicatorCount G J σ : ℝ) ^ j := by
      have h := (hbound (activeSites G J σ) (filter_subset _ _)).2
      rwa [card_activeSites] at h
    calc
      _ ≤ ((indicatorCount G J σ : ℝ) ^ j) ^ 8 := pow_le_pow_left₀ (hX σ) hboundX 8
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hprob : RetainedCountCylinder.badProbability H N L G =
      finiteExpectation (cylinderProbability M).weight (fun σ ↦ if B σ then 1 else 0) :=
    ActiveSetCylinder.event_probability G L (fun A ↦ ¬RetainedGoodEdges.Retained H N L A)
  have hmoment0 : 0 ≤ finiteExpectation (cylinderProbability M).weight (fun σ ↦ X σ ^ 8) :=
    sum_nonneg fun σ _ ↦ mul_nonneg ((cylinderProbability M).weight_nonneg σ) (pow_nonneg (hX σ) _)
  have hprob0 : 0 ≤ RetainedCountCylinder.badProbability H N L G := ENNReal.toReal_nonneg
  have h := ExceptionalEventHolder.restricted_eighth (cylinderProbability M) X hX B
  rw [← hprob] at h
  rw [finite_value]
  change finiteExpectation (cylinderProbability M).weight (fun σ ↦ if B σ then X σ else 0) ≤ _
  exact h.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hmoment0 hmoment (by norm_num))
    (Real.rpow_nonneg hprob0 _))

end PaperP1.ActiveSetExceptionalMoment
