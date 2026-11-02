module

public import PaperP1.Model.EvenValuePrescriptions
public import PaperP1.Model.PrivateNormalizedFamilyRank
public import PaperP1.Arithmetic.ConnectedValueUnions

/-! # Affine compatibility and exact family probabilities from full even rank alone -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenNormalizedFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.Model.InfiniteStarts PaperP1.RelativeSignIndependence PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem affine_witness {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L) :
    ∃ ω : InfiniteSample, ∀ i, infiniteStartBits (X i) L ω = startRhs L := by
  let b : valueUnion c X L → F₂ := fun n ↦ if n.val ∈ predecessors c X then 1 else 0
  obtain ⟨ω, δ, hω⟩ := EvenValuePrescriptions.prescribe_up_to_constant (valueUnion c X L) hfull b
  have hp (i : Fin r) : infiniteValueBit ω (c i * (X i - 1)) = 1 + δ := by
    have hh := hω ⟨c i * (X i - 1), predecessor_mem c X hX i⟩
    have hmem : c i * (X i - 1) ∈ predecessors c X := mem_image_of_mem _ (mem_univ i)
    simpa only [b, hmem, ite_true] using hh
  have hv (i : Fin r) (u : Fin L) : infiniteValueBit ω (c i * (X i + u.val)) = δ := by
    have hh := hω ⟨c i * (X i + u.val), internal_mem c X hX i u⟩
    simpa only [b, internal_not_predecessor hex i u, ite_false, zero_add] using hh
  have hp' (i : Fin r) : infiniteValueBit ω (c i) + infiniteValueBit ω (X i - 1) = 1 + δ := by
    have hh := hp i
    rwa [infiniteValueBit_mul ω (hc i).ne' (show X i - 1 ≠ 0 by have hh := hX i; omega)] at hh
  have hv' (i : Fin r) (u : Fin L) : infiniteValueBit ω (c i) + infiniteValueBit ω (X i + u.val) = δ := by
    have hh := hv i u
    rwa [infiniteValueBit_mul ω (hc i).ne' (show X i + u.val ≠ 0 by have hh := hX i; omega)] at hh
  have hzero (i : Fin r) : infiniteValueBit ω (c i) + infiniteValueBit ω (X i) = δ := by
    simpa only [Nat.add_zero] using hv' i ⟨0, hL⟩
  refine ⟨ω, fun i ↦ ?_⟩
  funext u
  by_cases hu : u.val = 0
  · have hh : infiniteValueBit ω (X i - 1) + infiniteValueBit ω (X i) = 1 :=
      (by decide : ∀ a b c δ : F₂, a + b = 1 + δ → a + c = δ → b + c = 1) _ _ _ _ (hp' i) (hzero i)
    simpa only [infiniteStartBits, startRhs, hu, ite_true] using hh
  · have hh : infiniteValueBit ω (X i) + infiniteValueBit ω (X i + u.val) = 0 :=
      (by decide : ∀ a b c δ : F₂, a + b = δ → a + c = δ → b + c = 0) _ _ _ _ (hzero i) (hv' i u)
    simpa only [infiniteStartBits, startRhs, hu, ite_false] using hh

theorem actual_joint_positive {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L) :
    0 < infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) := by
  obtain ⟨ω, hω⟩ := affine_witness c X hc hX hL hfull hex
  let M := (univ.sup X) + L
  have hcut : ∀ i, X i + L ≤ M := fun i ↦ Nat.add_le_add_right (le_sup (f := X) (mem_univ i)) L
  let a := PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M ω
  have hsystems : (fun i ↦ startSystem M (X i) L a) = (fun _ ↦ startRhs L) := by
    funext i
    exact (startSystem_restrict_eq (hcut i) ω).trans (hω i)
  have hpos := WindowFamilyConditional.source_mass_pos X a hcut
  rw [hsystems] at hpos
  change 0 < PrescribedTupleMass.joint L (fun _ ↦ startRhs L) X at hpos
  rwa [JointTupleSupport.prescribed_eq_support X hL] at hpos

theorem actual_joint_rank {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) =
      (2 ^ Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) : ℝ)⁻¹ := by
  have hpos := actual_joint_positive c X hc hX hL hfull hex
  rcases PrescribedTupleRank.joint_zero_or_rank (L := L) (fun _ ↦ startRhs L) X with hz | heq
  · rw [JointTupleSupport.prescribed_eq_support X hL] at hz
    exact False.elim ((ne_of_gt hpos) hz)
  · rwa [JointTupleSupport.prescribed_eq_support X hL] at heq

theorem local_ranks {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hfull : EvenIndependentValues.Independent (valueUnion c X L)) :
    ∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L := by
  intro i
  have hsub := hfull.mono (normalized_subset c X L i)
  have hh := EvenIndependentValues.finrank_space hsub
  rw [space_normalized (hc i) (hX i), card_normalized (hc i) (by have hh := hX i; omega), Nat.add_sub_cancel] at hh
  exact hh

theorem common_joint_rank {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L)
    (hfull : EvenIndependentValues.Independent (valueUnion c X L)) :
    Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) = (valueUnion c X L).card - 1 := by
  rw [← PrivateNormalizedFamilyRank.common_normalized_space hr c X hc hX a ha]
  exact EvenIndependentValues.finrank_space hfull

theorem common_probability {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L)
    (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = (2 ^ ((valueUnion c X L).card - 1) : ℝ)⁻¹ := by
  rw [actual_joint_rank c X hc hX hL hfull hex, common_joint_rank hr c X hc hX a ha hfull]

theorem connected_joint_rank {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hfull : EvenIndependentValues.Independent (valueUnion c X L))
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) = (valueUnion c X L).card - 1 := by
  have hh := ConnectedValueUnions.connected_union_space (fun i ↦ normalized (c i) (X i) L)
    (fun i ↦ normalized_nonempty (c i) (X i) L) hconn
  have hspaces : (fun i ↦ FiniteEvenSquareClasses.space (normalized (c i) (X i) L)) =
      (fun i ↦ squareClassSpace (X i) L) := funext (fun i ↦ space_normalized (hc i) (hX i))
  rw [hspaces] at hh
  rw [← hh]
  exact EvenIndependentValues.finrank_space hfull

theorem connected_probability {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L)
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = (2 ^ ((valueUnion c X L).card - 1) : ℝ)⁻¹ := by
  rw [actual_joint_rank c X hc hX hL hfull hex, connected_joint_rank c X hc hX hfull hconn]

theorem common_probability_nullity {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L)
    (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L) (ρ : ℕ)
    (hdim : (valueUnion c X L).card - 1 + ρ = r * L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ ρ : ℝ) := by
  rw [common_probability hr c X hc hX hL a ha hfull hex]
  exact PrivateNormalizedFamilyRank.rank_weight_identity L r _ ρ hdim

theorem connected_probability_nullity {r L : ℕ} (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (hfull : EvenIndependentValues.Independent (valueUnion c X L)) (hex : Exclusive c X L)
    (hconn : (ConnectedValueUnions.intersectionGraph (fun i ↦ normalized (c i) (X i) L)).Connected) (ρ : ℕ)
    (hdim : (valueUnion c X L).card - 1 + ρ = r * L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ ρ : ℝ) := by
  rw [connected_probability c X hc hX hL hfull hex hconn]
  exact PrivateNormalizedFamilyRank.rank_weight_identity L r _ ρ hdim

end PaperP1.EvenNormalizedFamilies
