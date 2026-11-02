module

public import PaperP1.Model.PrivateNormalizedFamilies
public import PaperP1.Arithmetic.PrivateEvenIntersection

/-! # Common normalized values identify the exact joint rank of any private finite family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateNormalizedFamilyRank

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedWindowSets PaperP1.FiniteEvenSquareClasses PaperP1.PrivateNormalizedFamilies

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem common_union_space {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → Finset ℕ)
    (a : ℕ) (ha : ∀ i, a ∈ A i) :
    space (univ.biUnion A) = ⨆ i, space (A i) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have haU : a ∈ univ.biUnion A := mem_biUnion.mpr ⟨i₀, mem_univ _, ha i₀⟩
  apply le_antisymm
  · rw [space_eq_span _ a haU]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨n, hn, rfl⟩ := hz
    obtain ⟨i, _hi, hnA⟩ := mem_biUnion.mp hn
    have hlocal : parityVec n - parityVec a ∈ space (A i) := by
      rw [space_eq_span (A i) a (ha i)]
      exact Submodule.subset_span ⟨n, hnA, rfl⟩
    exact (le_iSup (fun j ↦ space (A j)) i) hlocal
  · apply iSup_le
    intro i
    exact PrivateEvenIntersection.space_mono (subset_biUnion_of_mem A (mem_univ i))

theorem local_ranks {r L : ℕ} (c X : Fin r → ℕ) (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i)
    (hprivate : Private (valueUnion c X L)) : ∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L := by
  intro i
  have hpriv := hprivate.mono (normalized_subset c X L i)
  have hh := finrank_space (normalized (c i) (X i) L) hpriv
  rw [space_normalized (hc i) (hX i), card_normalized (hc i) (by have hh := hX i; omega), Nat.add_sub_cancel] at hh
  exact hh

theorem common_normalized_space {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L) :
    space (valueUnion c X L) = (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hh := common_union_space (fun i ↦ normalized (c i) (X i) L) a ha
  have hspaces : (fun i ↦ space (normalized (c i) (X i) L)) = (fun i ↦ squareClassSpace (X i) L) :=
    funext (fun i ↦ space_normalized (hc i) (hX i))
  change space (valueUnion c X L) = iSup (fun i ↦ space (normalized (c i) (X i) L)) at hh
  rwa [hspaces] at hh

theorem joint_rank {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L)
    (hprivate : Private (valueUnion c X L)) :
    Module.finrank F₂ (⨆ i, squareClassSpace (X i) L : Submodule F₂ (ℕ →₀ F₂)) =
      (valueUnion c X L).card - 1 := by
  rw [← common_normalized_space hr c X hc hX a ha]
  exact finrank_space _ hprivate

theorem actual_probability {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L)
    (hprivate : Private (valueUnion c X L)) (hex : Exclusive c X L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = (2 ^ ((valueUnion c X L).card - 1) : ℝ)⁻¹ := by
  rw [actual_joint_rank c X hc hX hL hprivate hex, joint_rank hr c X hc hX a ha hprivate]

theorem rank_weight_identity (L r R ρ : ℕ) (hdim : R + ρ = r * L) :
    (2 ^ R : ℝ)⁻¹ = ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ ρ : ℝ) := by
  have hfactor : (2 ^ R : ℝ) * 2 ^ ρ = (2 ^ L : ℝ) ^ r := by
    rw [← pow_add, hdim, Nat.mul_comm r L, pow_mul]
  rw [inv_pow]
  field_simp
  exact hfactor.symm

theorem probability_nullity {r L : ℕ} (hr : 0 < r) (c X : Fin r → ℕ)
    (hc : ∀ i, 0 < c i) (hX : ∀ i, 2 ≤ X i) (hL : 0 < L)
    (a : ℕ) (ha : ∀ i, a ∈ normalized (c i) (X i) L)
    (hprivate : Private (valueUnion c X L)) (hex : Exclusive c X L) (ρ : ℕ)
    (hdim : (valueUnion c X L).card - 1 + ρ = r * L) :
    infiniteJointMoment L (FiniteFamilyEnumeration.tupleSet X) = ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ ρ : ℝ) := by
  rw [actual_probability hr c X hc hX hL a ha hprivate hex]
  exact rank_weight_identity L r _ ρ hdim

end PaperP1.PrivateNormalizedFamilyRank
