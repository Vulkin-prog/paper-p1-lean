module

public import PaperP1.Affine.FamilyConditionalMass
public import Mathlib.LinearAlgebra.Span.Basic

/-! # Observing a source row span is exactly prescribing every compatible source event -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceFamilyEvent

open Finset PaperP1.Affine

local instance sourceFamilyEventDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V ι β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype β]

theorem effectiveEvent_iSup (S : ι → Submodule 𝔽₂ (Module.Dual 𝔽₂ V)) (a v : V) :
    effectiveEvent (⨆ i, S i) a v ↔ ∀ i, effectiveEvent (S i) a v := by
  constructor
  · intro h i f
    exact h ⟨f.val, (le_iSup S i) f.property⟩
  · intro h f
    exact Submodule.iSup_induction S (motive := fun g ↦ g v = g a) f.property
      (fun i g hg ↦ h i ⟨g, hg⟩) (by simp) (fun g k hg hk ↦ by simp only [LinearMap.add_apply, hg, hk])

theorem oldSpace_event (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a v : V) :
    effectiveEvent (FamilyConditionalMass.oldSpace A) a v ↔
      ∀ i : ι, A (some i) v = A (some i) a := by
  rw [FamilyConditionalMass.oldSpace, effectiveEvent_iSup]
  simp only [effectiveRowEvent_iff]

variable [Fintype V]

theorem observation_mass (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) :
    oldObservationMass (FamilyConditionalMass.oldSpace A) a =
      PaperP1.Algebra.finiteExpectation (PaperP1.Probability.uniformFiniteProbability V).weight
        (fun v ↦ if ∀ i : ι, A (some i) v = A (some i) a then (1 : ℝ) else 0) := by
  classical
  unfold oldObservationMass
  simp_rw [oldSpace_event]

theorem conditional_mass_ratio (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂) :
    FamilyConditionalMass.mass A a b =
      PaperP1.Algebra.finiteExpectation (PaperP1.Probability.uniformFiniteProbability V).weight
        (fun v ↦ if (∀ i : ι, A (some i) v = A (some i) a) ∧ A none v = b then (1 : ℝ) else 0) /
      PaperP1.Algebra.finiteExpectation (PaperP1.Probability.uniformFiniteProbability V).weight
        (fun v ↦ if ∀ i : ι, A (some i) v = A (some i) a then (1 : ℝ) else 0) := by
  classical
  unfold FamilyConditionalMass.mass conditionalAffineMass
  rw [observation_mass]
  simp_rw [oldSpace_event]

end PaperP1.SourceFamilyEvent
