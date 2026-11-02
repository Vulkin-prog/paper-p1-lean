module

public import PaperP1.Affine.RealProbability

/-! # Surjective linear precomposition preserves the actual uniform affine law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformPrecomposition

open PaperP1.Affine

variable {V W U : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
  [AddCommGroup W] [Module 𝔽₂ W] [Fintype W] [AddCommGroup U] [Module 𝔽₂ U]

local instance uniformPrecompositionTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

omit [Fintype V] [Fintype W] in
theorem range_comp (f : V →ₗ[𝔽₂] W) (hf : Function.Surjective f) (A : W →ₗ[𝔽₂] U) :
    LinearMap.range (A.comp f) = LinearMap.range A := by
  ext b
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨f v, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨v, rfl⟩

theorem mass_eq (f : V →ₗ[𝔽₂] W) (hf : Function.Surjective f) (A : W →ₗ[𝔽₂] U) (b : U) :
    uniformSolutionMass (A.comp f) b = uniformSolutionMass A b := by
  have hrange := range_comp f hf A
  have hcompat : Compatible (A.comp f) b ↔ Compatible A b := by
    simp only [Compatible, hrange]
  by_cases h : Compatible A b
  · rw [uniformSolutionMass_of_compatible _ b (hcompat.mpr h),
      uniformSolutionMass_of_compatible _ b h, hrange]
  · rw [uniformSolutionMass_of_not_compatible _ b (hcompat.not.mpr h),
      uniformSolutionMass_of_not_compatible _ b h]

end PaperP1.UniformPrecomposition
