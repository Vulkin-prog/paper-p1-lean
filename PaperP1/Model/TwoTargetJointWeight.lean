module

public import PaperP1.Model.BlockJointIntersection
public import PaperP1.Affine.TwoTargetCrossingCut
public import PaperP1.Model.TwoTargetPrimitiveData
public import PaperP1.Model.InfiniteTripleCancellation

/-! # Actual two-target joint bounds above arbitrary internally dependent old sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetJointWeight

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration
  PaperP1.TwoTargetWindowSections

local instance twoTargetJointPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem pair_kernel (L : ℕ) (e : Finset ℕ) (y z : ℕ) (hyz : y ≠ z) :
    MinimalRelativeRelations.nullity (sourceSpace e L) (fun x ↦ squareClassSpace x L) {y, z} =
      Module.finrank F₂ (Kernel y z L (sourceSpace e L)) := by
  let S := fun x ↦ squareClassSpace x L
  let W := sourceSpace e L
  let : Fintype W := MinimalRelativeRelations.spanFintype S e
  have hd : MinimalRelativeRelations.nullity W S {y, z} = TwoTargetDensePairs.deficit W y z L := by
    have h := TwoTargetCrossingCut.relative_nullity_eq_deficit S W ∅ y z (notMem_empty _) (notMem_empty _) hyz
      (MinimalRelativeRelations.nullity_empty W S)
    rw [span_empty, sup_bot_eq] at h
    exact h
  rw [TwoTargetDensePairs.deficit_eq_kernel (centres e rfl) L W (source_enumeration e L rfl).le] at hd
  exact hd

theorem intersection_le_kernel (L : ℕ) (e : Finset ℕ) (y z : ℕ) (hyz : y ≠ z) :
    Module.finrank F₂ ↥(sourceSpace e L ⊓ span (fun x ↦ squareClassSpace x L) {y, z}) ≤
      Module.finrank F₂ (Kernel y z L (sourceSpace e L)) := by
  let : Fintype (sourceSpace e L) := MinimalRelativeRelations.spanFintype (fun x ↦ squareClassSpace x L) e
  have h := RelativeIntersectionNullity.identity (fun x ↦ squareClassSpace x L) (sourceSpace e L) {y, z}
  rw [pair_kernel L e y z hyz] at h
  change Module.finrank F₂ (Kernel y z L (sourceSpace e L)) =
    relativeNullityOn (fun x ↦ squareClassSpace x L) {y, z} +
      Module.finrank F₂ ↥(sourceSpace e L ⊓ span (fun x ↦ squareClassSpace x L) {y, z}) at h
  omega

theorem joint_bound (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (y z : ℕ)
    (hy : y ∉ e) (hz : z ∉ e) (hyz : y ≠ z) :
    infiniteJointMoment L (TwoTargetFamilyCover.family e (y, z)) ≤
      infiniteJointMoment L e * (infiniteMarginal y L * infiniteMarginal z L *
        (2 ^ Module.finrank F₂ (Kernel y z L (sourceSpace e L)) : ℝ)) := by
  have hdis : Disjoint e ({y, z} : Finset ℕ) := by
    apply disjoint_left.mpr
    intro x hx hxy
    rcases mem_insert.mp hxy with rfl | hxz
    · exact hy hx
    · exact hz (mem_singleton.mp hxz ▸ hx)
  have heq : e ∪ {y, z} = TwoTargetFamilyCover.family e (y, z) := by
    ext x
    simp only [TwoTargetFamilyCover.family, mem_union, mem_insert, mem_singleton]
    tauto
  have h := ExtensionJointFactor.upper_bound L hL e {y, z} hdis
  rw [heq, prod_pair hyz] at h
  change infiniteJointMoment L (TwoTargetFamilyCover.family e (y, z)) ≤
    infiniteJointMoment L e * (infiniteMarginal y L * infiniteMarginal z L *
      (2 ^ MinimalRelativeRelations.nullity (sourceSpace e L) (fun x ↦ squareClassSpace x L) {y, z} : ℝ)) at h
  rw [pair_kernel L e y z hyz] at h
  exact h

theorem one_target_bound (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (y z : ℕ) (hy : y ∉ e)
    (hWY : Disjoint (sourceSpace e L) (squareClassSpace y L)) :
    infiniteJointMoment L (TwoTargetFamilyCover.family e (y, z)) ≤
      infiniteJointMoment L e * infiniteMarginal y L := by
  have hdis : Disjoint e ({y} : Finset ℕ) := disjoint_singleton_right.mpr hy
  have hspan : span (fun x ↦ squareClassSpace x L) {y} = squareClassSpace y L := by simp [span]
  have hzero : span (fun x ↦ squareClassSpace x L) e ⊓
      span (fun x ↦ squareClassSpace x L) {y} = ⊥ := by
    rw [hspan]
    exact hWY.eq_bot
  have h := BlockJointIntersection.upper_bound L hL e {y} hdis
  rw [hzero, finrank_bot, pow_zero, mul_one, InfiniteTripleCancellation.singleton_joint] at h
  apply (MissingBlockProbabilities.infiniteJointMoment_antitone L ?_).trans h
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · exact mem_insert_of_mem (mem_insert_of_mem hx)
  · exact (mem_singleton.mp hx) ▸ mem_insert_self _ _

end PaperP1.TwoTargetJointWeight
