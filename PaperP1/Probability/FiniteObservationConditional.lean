module

public import PaperP1.Probability.UniformFubini
public import PaperP1.Probability.MeasureFiniteLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Uniform finite observation laws give actual measure-theoretic conditional expectations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteObservationConditional

open MeasureTheory PaperP1.UniformFubini PaperP1.Probability

local instance finiteObservationConditionalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {Ω A B : Type*} [MeasurableSpace Ω]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
  [Fintype B] [Nonempty B] [MeasurableSpace B] [DiscreteMeasurableSpace B]

abbrev observationSigma (Z : Ω → A × B) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω ↦ (Z ω).1) inferInstance

theorem mean_is_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → A × B) (hZ : Measurable Z)
    (htransport : ∀ f : A × B → ℝ, (∫ ω, f (Z ω) ∂μ) = average f) (f : A × B → ℝ) :
    (fun ω ↦ average (fun b ↦ f ((Z ω).1, b))) =ᵐ[μ]
      condExp (observationSigma Z) μ (fun ω ↦ f (Z ω)) := by
  have hm : observationSigma Z ≤ ‹MeasurableSpace Ω› := hZ.fst.comap_le
  have hf : Integrable (fun ω ↦ f (Z ω)) μ :=
    (integrable_finite_function (μ.map Z) f).comp_measurable hZ
  have hg : Integrable (fun ω ↦ average (fun b ↦ f ((Z ω).1, b))) μ :=
    (integrable_finite_function (μ.map Z) (fun p ↦ average (fun b ↦ f (p.1, b)))).comp_measurable hZ
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s _ _
    exact hg.integrableOn
  · intro s hs _
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← integral_indicator (hZ.fst ht), ← integral_indicator (hZ.fst ht)]
    change (∫ ω, (if (Z ω).1 ∈ t then average (fun b ↦ f ((Z ω).1, b)) else 0) ∂μ) =
      ∫ ω, (if (Z ω).1 ∈ t then f (Z ω) else 0) ∂μ
    rw [htransport (fun p ↦ if p.1 ∈ t then average (fun b ↦ f (p.1, b)) else 0),
      htransport (fun p ↦ if p.1 ∈ t then f p else 0)]
    exact UniformFubini.set_average f t
  · exact ((Measurable.of_discrete : Measurable (fun a : A ↦ average (fun b ↦ f (a, b)))).comp
      (comap_measurable (fun ω ↦ (Z ω).1))).stronglyMeasurable.aestronglyMeasurable

end PaperP1.FiniteObservationConditional
