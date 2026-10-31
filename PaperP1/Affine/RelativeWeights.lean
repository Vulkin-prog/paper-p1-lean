module

public import PaperP1.Affine.FourierBound

/-!
# Exact relative-nullity weights

Multiplying the actual local affine rates by `2^ρ` gives the inverse size of
their total effective space. The equality uses rank-nullity, not equal local
ranks or a nominal Bernoulli parameter.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance relativeWeightsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

omit [Fintype ι] in
theorem effectiveRate_eq_inv_two_pow (i : ι) :
    effectiveRate (S i) = (2 ^ Module.finrank 𝔽₂ (S i) : ℝ)⁻¹ := by
  rw [effectiveRate, card_eq_two_pow_finrank (V := S i)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem relative_weight_eq_total_rank :
    (2 ^ relativeNullity S : ℝ) * (∏ i, effectiveRate (S i)) =
      (2 ^ Module.finrank 𝔽₂ (⨆ i, S i : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) : ℝ)⁻¹ := by
  simp_rw [effectiveRate_eq_inv_two_pow S]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum,
    relativeNullity_dimension_identity, pow_add, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

end PaperP1.Affine
