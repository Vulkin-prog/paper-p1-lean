module

public import PaperP1.Affine.CompatibleFullSupport
public import PaperP1.Affine.EffectiveRows
public import PaperP1.Probability.UniformFubini

/-! # Exact family event masses with actual heterogeneous marginals and relative kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FamilyEventMass

open Finset PaperP1.Affine PaperP1.UniformFubini

local instance familyEventMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance familyEventMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V ι β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [Fintype ι] [Fintype β]

def mass (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂) : ℝ :=
  average (fun v ↦ if ∀ i, A i v = b i then 1 else 0)

def CompatibleFamily (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂) : Prop :=
  ∃ a, ∀ i, A i a = b i

theorem of_witness (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂)
    (a : V) (ha : ∀ i, A i a = b i) :
    mass A b = (∏ i, effectiveRate (effectiveRowSpace (A i))) *
      (2 ^ relativeNullity (fun i ↦ effectiveRowSpace (A i)) : ℝ) := by
  classical
  let S := fun i ↦ effectiveRowSpace (A i)
  have heq : mass A b = effectiveJointMoment S (fun _ ↦ a) := by
    unfold mass effectiveJointMoment
    apply UniformFubini.congr
    intro v
    simp only [effectiveIndicator, S, effectiveRowEvent_iff, ha, Fintype.prod_boole]
  rw [heq]
  exact compatible_joint_count S a

theorem of_incompatible (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂)
    (h : ¬CompatibleFamily A b) : mass A b = 0 := by
  have hv (v : V) : ¬∀ i, A i v = b i := fun hv ↦ h ⟨v, hv⟩
  unfold mass
  simp only [hv, ite_false, UniformFubini.constant]

theorem exact_marginal_formula (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂) :
    mass A b = (if CompatibleFamily A b then (1 : ℝ) else 0) *
      (∏ i, uniformSolutionMass (A i) (b i)) *
      (2 ^ relativeNullity (fun i ↦ effectiveRowSpace (A i)) : ℝ) := by
  classical
  by_cases h : CompatibleFamily A b
  · obtain ⟨a, ha⟩ := h
    rw [ite_eq_left (show CompatibleFamily A b from ⟨a, ha⟩), one_mul, of_witness A b a ha]
    congr 1
    apply prod_congr rfl
    intro i _
    exact (compatible_mass_eq_effectiveRate (A i) (b i) (LinearMap.mem_range.mpr ⟨a, ha i⟩)).symm
  · rw [of_incompatible A b h, ite_eq_right h, zero_mul, zero_mul]

end PaperP1.FamilyEventMass
