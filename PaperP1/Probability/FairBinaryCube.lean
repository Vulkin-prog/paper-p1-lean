module

public import PaperP1.Algebra.DotTranspose
public import PaperP1.Model.InfiniteRademacher
public import PaperP1.Probability.MeasureFiniteLaw

/-! # Exact fair-cube pushforwards of injective transposed coordinate maps -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FairBinaryCube

open MeasureTheory PaperP1.Affine PaperP1.Algebra PaperP1.Probability
  PaperP1.Model.InfiniteRademacher PaperP1.DotTranspose

local instance fairBinaryMeasurableF2 : MeasurableSpace 𝔽₂ := ⊤
local instance fairBinaryDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def measure (ι : Type*) [Fintype ι] : Measure (ι → 𝔽₂) := Measure.pi fun _ ↦ coordinateMeasure

instance measure_probability (ι : Type*) [Fintype ι] : IsProbabilityMeasure (measure ι) := by
  unfold measure
  infer_instance

theorem real_singleton {ι : Type*} [Fintype ι] (b : ι → 𝔽₂) :
    (measure ι).real {b} = (2 ^ Fintype.card ι : ℝ)⁻¹ := by
  rw [measure, Measure.real, Measure.pi_singleton]
  simp [coordinateMeasure, Measure.uniformOfFinset_apply_singleton, ZMod.card]

theorem weights_eq_uniform (ι : Type*) [Fintype ι] :
    (finiteProbabilityOfMeasure (measure ι)).weight = (uniformFiniteProbability (ι → 𝔽₂)).weight := by
  funext b
  change (measure ι).real {b} = (Fintype.card (ι → 𝔽₂) : ℝ)⁻¹
  rw [real_singleton]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]

theorem event_eq_affine {α β : Type*} [Fintype α] [Fintype β]
    (A : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    (measure α).real {v | A v = b} = uniformSolutionMass A b := by
  rw [← finiteMeasure_indicator_expectation]
  unfold uniformSolutionMass
  rw [weights_eq_uniform]
  apply congrArg (finiteExpectation (uniformFiniteProbability (α → 𝔽₂)).weight)
  funext v
  split_ifs <;> rfl

theorem map_transpose_eq {α β : Type*} [Fintype α] [Fintype β]
    (c : (α → 𝔽₂) →ₗ[𝔽₂] (β → 𝔽₂)) (hc : Function.Injective c) :
    (measure β).map (transpose c) = measure α := by
  apply Measure.ext_of_singleton
  intro b
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton b)]
  change (measure β).real {v | transpose c v = b} = _
  rw [event_eq_affine, uniformSolutionMass_of_injective_relationMap _ (relationMap_injective c hc), real_singleton]
  simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]

end PaperP1.FairBinaryCube
