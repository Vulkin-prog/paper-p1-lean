module

public import PaperP1.Affine.Probability
public import PaperP1.Probability.UniformFinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine probabilities under the constructed real uniform law

Incompatibility has zero mass. A compatible system has mass `2⁻ʳ`, where
`r` is its effective rank, rather than its nominal number of rows.
-/

@[expose] public noncomputable section

open PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Affine

variable {V W : Type*}
variable [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
variable [AddCommGroup W] [Module 𝔽₂ W]

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

local instance realSolutionFintype (A : V →ₗ[𝔽₂] W) (b : W) :
    Fintype (Solution A b) := Fintype.ofFinite _

local instance realCompatibleDecidable (A : V →ₗ[𝔽₂] W) (b : W) :
    Decidable (Compatible A b) := Classical.propDecidable _

/-- Actual real probability, defined from the normalized uniform weights. -/
def uniformSolutionMass (A : V →ₗ[𝔽₂] W) (b : W) : ℝ := by
  classical
  exact finiteExpectation (uniformFiniteProbability V).weight
    (fun v => if A v = b then 1 else 0)

theorem uniformSolutionMass_eq_card_ratio (A : V →ₗ[𝔽₂] W) (b : W) :
    uniformSolutionMass A b =
      (Fintype.card (Solution A b) : ℝ) / Fintype.card V := by
  classical
  rw [uniformSolutionMass, uniformFiniteExpectation_indicator]
  congr 1
  exact congrArg (fun n : ℕ => (n : ℝ))
    (Fintype.card_subtype (fun v => v ∈ solutionSet A b)).symm

theorem uniformSolutionMass_eq_ite (A : V →ₗ[𝔽₂] W) (b : W) :
    uniformSolutionMass A b =
      if Compatible A b then
        (2 ^ Module.finrank 𝔽₂ (LinearMap.ker A) : ℝ) /
          (2 ^ Module.finrank 𝔽₂ V : ℝ)
      else 0 := by
  classical
  rw [uniformSolutionMass_eq_card_ratio, card_solution_eq_ite,
    card_eq_two_pow_finrank (V := V)]
  split_ifs <;> simp_all

theorem uniformSolutionMass_of_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : Compatible A b) :
    uniformSolutionMass A b = (2 ^ Module.finrank 𝔽₂ (LinearMap.range A) : ℝ)⁻¹ := by
  rw [uniformSolutionMass_eq_ite, ite_eq_left h,
    ← A.finrank_range_add_finrank_ker, pow_add]
  rw [mul_comm, div_mul_cancel_left₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]

theorem uniformSolutionMass_of_not_compatible
    (A : V →ₗ[𝔽₂] W) (b : W) (h : ¬Compatible A b) :
    uniformSolutionMass A b = 0 := by
  rw [uniformSolutionMass_eq_ite, ite_eq_right h]

theorem uniformSolutionMass_pos_iff (A : V →ₗ[𝔽₂] W) (b : W) :
    0 < uniformSolutionMass A b ↔ Compatible A b := by
  classical
  by_cases h : Compatible A b
  · rw [uniformSolutionMass_of_compatible A b h]
    exact iff_of_true (inv_pos.mpr (pow_pos (by norm_num) _)) h
  · rw [uniformSolutionMass_of_not_compatible A b h]
    exact iff_of_false (lt_irrefl 0) h

end PaperP1.Affine
