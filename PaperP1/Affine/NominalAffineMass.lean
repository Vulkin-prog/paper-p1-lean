module

public import PaperP1.Affine.EffectiveRows
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! # Exact nominal-row mass, with every row relation and incompatibility retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NominalAffineMass

open PaperP1.Affine

local instance nominalAffineMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance nominalAffineMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [Fintype β]

theorem compatible (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) (h : Compatible A b) :
    uniformSolutionMass A b =
      (2 ^ Module.finrank 𝔽₂ (LinearMap.ker (relationMap A)) : ℝ) / (2 ^ Fintype.card β : ℝ) := by
  classical
  rw [compatible_mass_eq_effectiveRate A b h, effectiveRate,
    card_eq_two_pow_finrank (V := effectiveRowSpace A)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hrank := (relationMap A).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) hrank
  rw [pow_add] at hpow
  change (2 ^ Module.finrank 𝔽₂ (effectiveRowSpace A) : ℝ) *
    2 ^ Module.finrank 𝔽₂ (LinearMap.ker (relationMap A)) = 2 ^ Fintype.card β at hpow
  field_simp
  nlinarith only [hpow]

theorem exact_formula (A : V →ₗ[𝔽₂] (β → 𝔽₂)) (b : β → 𝔽₂) :
    uniformSolutionMass A b =
      (if Compatible A b then (1 : ℝ) else 0) *
      (2 ^ Module.finrank 𝔽₂ (LinearMap.ker (relationMap A)) : ℝ) / (2 ^ Fintype.card β : ℝ) := by
  by_cases h : Compatible A b
  · rw [ite_eq_left h, one_mul]
    exact compatible A b h
  · rw [ite_eq_right h, zero_mul, zero_div]
    exact uniformSolutionMass_of_not_compatible A b h

end PaperP1.NominalAffineMass
