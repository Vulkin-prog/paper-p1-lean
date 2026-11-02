module

public import PaperP1.Model.PrivateValuePrescriptions
public import PaperP1.Model.PrescribedTupleRank
public import PaperP1.Model.JointTupleSupport
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Actual affine compatibility and exact rank probabilities for private normalized window families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateNormalizedFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.Model.InfiniteRademacher PaperP1.Model.InfiniteStarts
  PaperP1.RelativeSignIndependence PaperP1.NormalizedWindowSets

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def valueUnion {r : ℕ} (c X : Fin r → ℕ) (L : ℕ) : Finset ℕ :=
  univ.biUnion fun i ↦ normalized (c i) (X i) L

def predecessors {r : ℕ} (c X : Fin r → ℕ) : Finset ℕ := univ.image fun i ↦ c i * (X i - 1)

def Exclusive {r : ℕ} (c X : Fin r → ℕ) (L : ℕ) : Prop :=
  ∀ i j : Fin r, ∀ u : Fin L, c i * (X i - 1) ≠ c j * (X j + u.val)

theorem normalized_subset {r : ℕ} (c X : Fin r → ℕ) (L : ℕ) (i : Fin r) :
    normalized (c i) (X i) L ⊆ valueUnion c X L := by
  change normalized (c i) (X i) L ⊆ univ.biUnion (fun j ↦ normalized (c j) (X j) L)
  intro n hn
  exact mem_biUnion.mpr ⟨i, mem_univ _, hn⟩

theorem predecessor_mem {r L : ℕ} (c X : Fin r → ℕ) (hX : ∀ i, 2 ≤ X i) (i : Fin r) :
    c i * (X i - 1) ∈ valueUnion c X L := by
  apply normalized_subset c X L i
  apply mem_image.mpr
  refine ⟨X i - 1, mem_values.mpr ⟨⟨0, by omega⟩, ?_⟩, rfl⟩
  rw [startCompleteVertexLabel_eq_offset (by have hh := hX i; omega)]
  simp only [Nat.add_zero]

theorem internal_mem {r L : ℕ} (c X : Fin r → ℕ) (hX : ∀ i, 2 ≤ X i) (i : Fin r) (u : Fin L) :
    c i * (X i + u.val) ∈ valueUnion c X L := by
  apply normalized_subset c X L i
  apply mem_image.mpr
  refine ⟨X i + u.val, mem_values.mpr ⟨⟨u.val + 1, by have hh := u.isLt; omega⟩, ?_⟩, rfl⟩
  rw [startCompleteVertexLabel_eq_offset (by have hh := hX i; omega)]
  dsimp only
  have hh := hX i
  omega

theorem internal_not_predecessor {r L : ℕ} {c X : Fin r → ℕ} (hex : Exclusive c X L)
    (i : Fin r) (u : Fin L) : c i * (X i + u.val) ∉ predecessors c X := by
  intro hh
  obtain ⟨j, _hj, heq⟩ := mem_image.mp hh
  exact hex j i u heq

theorem affine_witness {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hprivate : FiniteEvenSquareClasses.Private (valueUnion c X L)) (hex : Exclusive c X L) :
    ∃ ω : InfiniteSample, ∀ i, infiniteStartBits (X i) L ω = startRhs L := by
  let b : valueUnion c X L → F₂ := fun n ↦ if n.val ∈ predecessors c X then 1 else 0
  obtain ⟨ω, hω⟩ := PrivateValuePrescriptions.prescribe (valueUnion c X L) hprivate b
  have hp (i : Fin r) : infiniteValueBit ω (c i * (X i - 1)) = 1 := by
    have hh := hω ⟨c i * (X i - 1), predecessor_mem c X hX i⟩
    have hmem : c i * (X i - 1) ∈ predecessors c X := mem_image_of_mem _ (mem_univ i)
    simpa only [b, hmem, ite_true] using hh
  have hv (i : Fin r) (u : Fin L) : infiniteValueBit ω (c i * (X i + u.val)) = 0 := by
    have hh := hω ⟨c i * (X i + u.val), internal_mem c X hX i u⟩
    simpa only [b, internal_not_predecessor hex i u, ite_false] using hh
  have hv' (i : Fin r) (u : Fin L) : infiniteValueBit ω (X i + u.val) = infiniteValueBit ω (c i) := by
    have hh := hv i u
    rw [infiniteValueBit_mul ω (hc i).ne' (show X i + u.val ≠ 0 by have hh := hX i; omega)] at hh
    exact (by decide : ∀ a b : F₂, a + b = 0 → b = a) _ _ hh
  have hv0 (i : Fin r) : infiniteValueBit ω (X i) = infiniteValueBit ω (c i) := by
    simpa only [Nat.add_zero] using hv' i ⟨0, hL⟩
  refine ⟨ω, fun i ↦ ?_⟩
  funext u
  by_cases hu : u.val = 0
  · have hh := hp i
    rw [infiniteValueBit_mul ω (hc i).ne' (show X i - 1 ≠ 0 by have hh := hX i; omega)] at hh
    simpa only [infiniteStartBits, startRhs, hu, ite_true, hv0 i, add_comm] using hh
  · simp only [infiniteStartBits, startRhs, hu, ite_false, hv0 i, hv' i u]
    exact (by decide : ∀ z : F₂, z + z = 0) _

theorem actual_joint_positive {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hL : 0 < L) (hprivate : FiniteEvenSquareClasses.Private (valueUnion c X L)) (hex : Exclusive c X L) :
    0 < infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) := by
  obtain ⟨ω, hω⟩ := affine_witness c X hc hX hL hprivate hex
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
    (hL : 0 < L) (hprivate : FiniteEvenSquareClasses.Private (valueUnion c X L)) (hex : Exclusive c X L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) =
      (2 ^ Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) : ℝ)⁻¹ := by
  have hpos := actual_joint_positive c X hc hX hL hprivate hex
  rcases PrescribedTupleRank.joint_zero_or_rank (L := L) (fun _ ↦ startRhs L) X with hz | heq
  · rw [JointTupleSupport.prescribed_eq_support X hL] at hz
    exact False.elim ((ne_of_gt hpos) hz)
  · rwa [JointTupleSupport.prescribed_eq_support X hL] at heq

end PaperP1.PrivateNormalizedFamilies
