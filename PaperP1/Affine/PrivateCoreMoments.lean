module

public import PaperP1.Affine.PrivateRankPositiveMass
public import PaperP1.Affine.PrivateRankCore
public import PaperP1.Affine.CommonAffineWitness

/-! # Original affine moments on every canonical component of the peeled family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateCoreMoments

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

def componentJoint (a : ι → V) {B : Finset ι} (C : Finset B) : ℝ :=
  effectiveJointMoment (fun i : C ↦ S i.val.val) (fun i ↦ a i.val.val)

def componentCentered (a : ι → V) {B : Finset ι} (C : Finset B) : ℝ :=
  effectiveCenteredMoment (fun i : C ↦ S i.val.val) (fun i ↦ a i.val.val)

def ComponentMassConclusion (A B : Finset ι) (a : ι → V) (L t : ℕ) : Prop :=
  ∀ C : (canonicalRelationPartition (fun i : B ↦ S i.val)).parts,
    (1 - (C.val.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t) * componentJoint S a C.val ≤ componentCentered S a C.val ∧
    (1 - (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t) * componentJoint S a C.val ≤
      (1 - (C.val.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t) * componentJoint S a C.val ∧
    (1 - (C.val.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ (t - 1)) * componentJoint S a C.val ≤ componentCentered S a C.val

theorem component_mass_bounds (A B : Finset ι) (hBA : B ⊆ A) (a : ι → V) (L t : ℕ)
    (hL : ∀ i ∈ A, Module.finrank 𝔽₂ (S i) = L) (hstop : ∀ i ∈ B, privateRank S B i < t)
    (hcompatible : ∃ b : V, ∀ i ∈ A, effectiveEvent (S i) (a i) b) :
    ComponentMassConclusion S A B a L t := by
  classical
  obtain ⟨b, hb⟩ := hcompatible
  let T : B → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂) := fun i ↦ S i.val
  let P := canonicalRelationPartition T
  have hP : RelationDirectPartition T P := canonicalRelationPartition_respects T
  intro C
  have hTC (j : B) (_hj : j ∈ C.val) : Module.finrank 𝔽₂ (T j) = L := hL j.val (hBA j.property)
  have hstopC (j : B) (hj : j ∈ C.val) : privateRank T C.val j < t := by
    rw [privateRank_in_part T P hP C hj, privateRank_subtype S B j]
    exact hstop j.val j.property
  have hweak := privateRank_centered_lower T C.val b L t hTC hstopC
  have hsharp := privateRank_centered_lower_sharp T C.val b L t hTC hstopC
  have hq : componentJoint S a C.val = effectiveJointMoment (fun j : C.val ↦ T j.val) (fun _ ↦ b) := by
    exact effectiveJointMoment_common_witness (fun j : C.val ↦ T j.val)
      (fun j ↦ a j.val.val) b (fun j ↦ hb j.val.val (hBA j.val.property))
  have hc : componentCentered S a C.val = effectiveCenteredMoment (fun j : C.val ↦ T j.val) (fun _ ↦ b) := by
    exact effectiveCenteredMoment_common_witness (fun j : C.val ↦ T j.val)
      (fun j ↦ a j.val.val) b (fun j ↦ hb j.val.val (hBA j.val.property))
  have hq0 : 0 ≤ componentJoint S a C.val := by
    rw [hq]
    exact compatible_joint_nonneg (fun j : C.val ↦ T j.val) b
  have hcardB : C.val.card ≤ B.card := by simpa only [Fintype.card_coe] using card_le_univ C.val
  have hcardA : (C.val.card : ℝ) ≤ A.card := by exact_mod_cast hcardB.trans (card_le_card hBA)
  have hcost : (C.val.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t ≤
      (A.card : ℝ) * (2 ^ L : ℝ)⁻¹ * 2 ^ t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcardA (by positivity)) (by positivity)
  refine ⟨?_, mul_le_mul_of_nonneg_right (by linarith) hq0, ?_⟩
  · rw [hq, hc]
    exact hweak
  · rw [hq, hc]
    exact hsharp

end PaperP1.PrivateCoreMoments
