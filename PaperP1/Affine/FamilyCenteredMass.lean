module

public import PaperP1.Affine.FamilyEventMass

/-! # Every compatible binary affine family has a nonnegative centered coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FamilyCenteredMass

open Finset PaperP1.Affine PaperP1.UniformFubini

local instance familyCenteredMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance familyCenteredMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V ι β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [Fintype ι] [Fintype β]

def centered (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂) : ℝ :=
  average (fun v ↦ ∏ i, ((if A i v = b i then (1 : ℝ) else 0) - uniformSolutionMass (A i) (b i)))

theorem of_witness (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂)
    (a : V) (ha : ∀ i, A i a = b i) :
    centered A b = (∏ i, uniformSolutionMass (A i) (b i)) *
      ((fullSupportRelations (fun i ↦ effectiveRowSpace (A i))).card : ℝ) := by
  classical
  let S := fun i ↦ effectiveRowSpace (A i)
  have hlocal (i : ι) : uniformSolutionMass (A i) (b i) = effectiveRate (S i) :=
    compatible_mass_eq_effectiveRate _ _ (LinearMap.mem_range.mpr ⟨a, ha i⟩)
  have heq : centered A b = effectiveCenteredMoment S (fun _ ↦ a) := by
    unfold centered effectiveCenteredMoment
    apply UniformFubini.congr
    intro v
    apply prod_congr rfl
    intro i _
    rw [hlocal, affineIndicator_eq_effectiveIndicator (A i) (b i) a v (ha i)]
  rw [heq, compatible_centered_count]
  simp_rw [hlocal]
  rfl

omit [Fintype V] in
theorem full_support_cardinality (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) :
    (fullSupportRelations (fun i ↦ effectiveRowSpace (A i))).card =
      Nat.card {s : (i : ι) → effectiveRowSpace (A i) //
        IsFullSupportRelation (fun i ↦ effectiveRowSpace (A i)) s} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem of_witness_cardinality (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂)
    (a : V) (ha : ∀ i, A i a = b i) :
    centered A b = (∏ i, uniformSolutionMass (A i) (b i)) *
      (Nat.card {s : (i : ι) → effectiveRowSpace (A i) //
        IsFullSupportRelation (fun i ↦ effectiveRowSpace (A i)) s} : ℝ) := by
  rw [of_witness A b a ha, full_support_cardinality]

theorem nonneg_of_witness (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂)
    (a : V) (ha : ∀ i, A i a = b i) : 0 ≤ centered A b := by
  rw [of_witness A b a ha]
  apply mul_nonneg _ (Nat.cast_nonneg _)
  apply prod_nonneg
  intro i _
  exact ((uniformSolutionMass_pos_iff (A i) (b i)).mpr (LinearMap.mem_range.mpr ⟨a, ha i⟩)).le

theorem nonneg_of_compatible (A : ι → V →ₗ[𝔽₂] (β → 𝔽₂)) (b : ι → β → 𝔽₂)
    (h : FamilyEventMass.CompatibleFamily A b) : 0 ≤ centered A b := by
  obtain ⟨a, ha⟩ := h
  exact nonneg_of_witness A b a ha

end PaperP1.FamilyCenteredMass
