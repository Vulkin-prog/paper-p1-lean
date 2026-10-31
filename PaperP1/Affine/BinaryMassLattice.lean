module

public import PaperP1.Affine.RealProbability

/-! # The exact dyadic lattice of an affine binary probability -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

variable {V W : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
variable [AddCommGroup W] [Module 𝔽₂ W]

local instance binaryMassLatticePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem uniformSolutionMass_integer_multiple (A : V →ₗ[𝔽₂] W) (b : W)
    (m : ℕ) (hrank : Module.finrank 𝔽₂ (LinearMap.range A) ≤ m) :
    ∃ k : ℕ, uniformSolutionMass A b = (k : ℝ) * (2 ^ m : ℝ)⁻¹ := by
  classical
  by_cases hc : Compatible A b
  · let r := Module.finrank 𝔽₂ (LinearMap.range A)
    refine ⟨2 ^ (m - r), ?_⟩
    rw [uniformSolutionMass_of_compatible A b hc]
    have hpow : (2 ^ m : ℝ) = (2 ^ r : ℝ) * (2 ^ (m - r) : ℝ) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [hpow]
    field_simp
    rfl
  · exact ⟨0, by rw [uniformSolutionMass_of_not_compatible A b hc]; simp⟩

end PaperP1.Affine
