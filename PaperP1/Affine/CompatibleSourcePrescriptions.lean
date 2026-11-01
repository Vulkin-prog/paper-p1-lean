module

public import PaperP1.Affine.SourceFamilyEvent
public import PaperP1.Probability.UniformFinite

/-! # Literal positive source-event probabilities and compatible witnesses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleSourcePrescriptions

open Finset PaperP1.Affine PaperP1.Algebra PaperP1.Probability

local instance compatibleSourcePrescriptionsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V ι β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype β] [Fintype V]

def sourceMass (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂) : ℝ :=
  finiteExpectation (uniformFiniteProbability V).weight
    (fun v ↦ if ∀ i, A (some i) v = b i then 1 else 0)

def conditionalProbability (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (b : ι → β → 𝔽₂) (c : β → 𝔽₂) : ℝ :=
  finiteExpectation (uniformFiniteProbability V).weight
    (fun v ↦ if (∀ i, A (some i) v = b i) ∧ A none v = c then 1 else 0) / sourceMass A b

theorem source_mass_of_witness (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (b : ι → β → 𝔽₂) (a : V) (ha : ∀ i, A (some i) a = b i) :
    sourceMass A b = oldObservationMass (FamilyConditionalMass.oldSpace A) a := by
  rw [SourceFamilyEvent.observation_mass]
  simp only [sourceMass, ha]

theorem source_mass_pos_iff (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂) :
    0 < sourceMass A b ↔ ∃ a, ∀ i, A (some i) a = b i := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hz : sourceMass A b = 0 := by
      unfold sourceMass finiteExpectation
      simp only [not_forall.mpr (hn _), ite_false, mul_zero, sum_const_zero]
    rw [hz] at h
    exact lt_irrefl _ h
  · rintro ⟨a, ha⟩
    rw [source_mass_of_witness A b a ha]
    exact oldObservationMass_pos _ _

theorem conditional_of_witness (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (b : ι → β → 𝔽₂) (c : β → 𝔽₂) (a : V) (ha : ∀ i, A (some i) a = b i) :
    conditionalProbability A b c = FamilyConditionalMass.mass A a c := by
  rw [SourceFamilyEvent.conditional_mass_ratio]
  simp only [conditionalProbability, sourceMass, ha]

end PaperP1.CompatibleSourcePrescriptions
