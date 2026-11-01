module

public import PaperP1.Affine.ConditionalMass
public import PaperP1.Affine.ExtensionRankBudget

/-! # Conditional affine masses with the exact effective-family nullity increment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FamilyConditionalMass

open Finset PaperP1.Affine

local instance familyConditionalTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V ι β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [Fintype ι] [Fintype β]

local instance familyConditionalDualFinite : Finite (V →ₗ[𝔽₂] 𝔽₂) :=
  Finite.of_injective (fun f : V →ₗ[𝔽₂] 𝔽₂ ↦ (f : V → 𝔽₂)) DFunLike.coe_injective
local instance familyConditionalSubspaceFintype (S : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) : Fintype S :=
  Fintype.ofFinite _

abbrev rows (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) := fun i ↦ effectiveRowSpace (A i)

def oldSpace (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂) :=
  ⨆ i : ι, effectiveRowSpace (A (some i))

def increment (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) : ℕ := ExtensionRankBudget.increment (rows A)

def mass (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂) : ℝ :=
  conditionalAffineMass (oldSpace A) a (A none) b

theorem kernel_rank_identity (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) :
    Module.finrank 𝔽₂ ((oldSpace A).comap (relationMap (A none))) +
      Module.finrank 𝔽₂ (effectiveRowSpace (A none)) = Fintype.card β + increment A := by
  have hjoined := PaperP1.QuotientRank.joined_rank_add_kernel (oldSpace A) (relationMap (A none))
  rw [Module.finrank_fintype_fun_eq_card] at hjoined
  have hinc := ExtensionRankBudget.total_rank_identity (rows A)
  rw [iSup_option, sup_comm] at hinc
  change Module.finrank 𝔽₂ (oldSpace A ⊔ effectiveRowSpace (A none) : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) + increment A =
    Module.finrank 𝔽₂ (oldSpace A) + Module.finrank 𝔽₂ (effectiveRowSpace (A none)) at hinc
  change Module.finrank 𝔽₂ (oldSpace A ⊔ effectiveRowSpace (A none) : Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) +
    Module.finrank 𝔽₂ ((oldSpace A).comap (relationMap (A none))) =
      Module.finrank 𝔽₂ (oldSpace A) + Fintype.card β at hjoined
  omega

omit [Fintype ι] in
theorem mass_nonneg (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂) :
    0 ≤ mass A a b := conditionalAffineMass_nonneg _ _ _ _

omit [Fintype ι] in
theorem mass_le_one (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂) :
    mass A a b ≤ 1 := conditionalAffineMass_le_one _ _ _ _

theorem mass_zero_or_effective_rate (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂) :
    mass A a b = 0 ∨ mass A a b = (2 ^ increment A : ℝ) *
      (2 ^ Module.finrank 𝔽₂ (effectiveRowSpace (A none)) : ℝ)⁻¹ := by
  rcases conditionalAffineMass_zero_or_pow (oldSpace A) a (A none) b with hz | hq
  · exact Or.inl hz
  apply Or.inr
  change mass A a b = _ at hq
  rw [hq]
  have hpow := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) (kernel_rank_identity A)
  rw [pow_add, pow_add] at hpow
  have hden : (2 ^ Fintype.card β : ℝ) ≠ 0 := by positivity
  have hrank : (2 ^ Module.finrank 𝔽₂ (effectiveRowSpace (A none)) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith only [hpow]

theorem mass_le_effective_rate (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂) :
    mass A a b ≤ (2 ^ increment A : ℝ) * (2 ^ Module.finrank 𝔽₂ (effectiveRowSpace (A none)) : ℝ)⁻¹ := by
  rcases mass_zero_or_effective_rate A a b with hz | hq
  · rw [hz]; positivity
  · exact hq.le

theorem mass_le_nominal (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (a : V) (b : β → 𝔽₂)
    (e : ℕ) (hdefect : Fintype.card β ≤ Module.finrank 𝔽₂ (effectiveRowSpace (A none)) + e) :
    mass A a b ≤ (2 ^ e : ℝ) * (2 ^ increment A : ℝ) / (2 ^ Fintype.card β : ℝ) := by
  have hkernel : Module.finrank 𝔽₂ ((oldSpace A).comap (relationMap (A none))) ≤ increment A + e := by
    have h := kernel_rank_identity A
    omega
  rcases conditionalAffineMass_zero_or_pow (oldSpace A) a (A none) b with hz | hq
  · change mass A a b = 0 at hz
    rw [hz]
    positivity
  · change mass A a b = _ at hq
    rw [hq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [pow_add, mul_comm] using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hkernel)

end PaperP1.FamilyConditionalMass
