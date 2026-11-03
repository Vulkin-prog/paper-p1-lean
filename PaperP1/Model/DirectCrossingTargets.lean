module

public import PaperP1.Model.ExtensionJointFactor
public import PaperP1.Affine.TwoTargetCrossingCut
public import PaperP1.Model.TwoTargetPrimitiveData
public import PaperP1.Model.CompatibleNullityBound

/-! # Actual minimal direct crossings have the precise two-target kernel and joint weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectCrossingTargets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.TwoTargetPrimitiveData PaperP1.FiniteFamilyEnumeration
  PaperP1.TwoTargetWindowSections

local instance directCrossingPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

theorem union_family (e B : Finset ℕ) (p : ℕ × ℕ) :
    e ∪ TwoTargetFamilyCover.family B p = TwoTargetFamilyCover.family (e ∪ B) p := by
  ext x
  simp only [TwoTargetFamilyCover.family, mem_union, mem_insert]
  tauto

theorem data {s y z L : ℕ} (e B : Finset ℕ) (hcard : (e ∪ B).card = s)
    (hy : y ∉ e ∪ B) (hz : z ∉ e ∪ B) (hyz : y ≠ z)
    (hzero : runRelativeNullity L (TwoTargetFamilyCover.family B (y, z)) = 0)
    (hproper : ∀ C : Finset ℕ, C ⊂ TwoTargetFamilyCover.family B (y, z) →
      Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) C)) :
    Disjoint (sourceSpace (e ∪ B) L) (squareClassSpace y L) ∧
      Disjoint (sourceSpace (e ∪ B) L) (squareClassSpace z L) ∧
      Disjoint (squareClassSpace y L) (squareClassSpace z L) ∧
      MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) e)
        (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family B (y, z)) =
          Module.finrank F₂ (Kernel y z L (sourceSpace (e ∪ B) L)) := by
  let S := fun x ↦ squareClassSpace x L
  let W := span S e
  let : Fintype W := MinimalRelativeRelations.spanFintype S e
  have hyB : y ∉ B := fun h ↦ hy (mem_union_right _ h)
  have hzB : z ∉ B := fun h ↦ hz (mem_union_right _ h)
  obtain ⟨hY, hZ, hYZ, hnull⟩ := TwoTargetCrossingCut.data S W B y z hyB hzB hyz hzero hproper
  have hsource : sourceSpace (e ∪ B) L = W ⊔ span S B := RetainedNullity.span_union S e B
  have hdeficit : MinimalRelativeRelations.nullity W S (TwoTargetFamilyCover.family B (y, z)) =
      TwoTargetDensePairs.deficit (sourceSpace (e ∪ B) L) y z L := by
    rw [← hsource] at hnull
    exact hnull
  rw [TwoTargetDensePairs.deficit_eq_kernel (centres (e ∪ B) hcard) L (sourceSpace (e ∪ B) L)
    (source_enumeration (e ∪ B) L hcard).le] at hdeficit
  exact ⟨by simpa only [hsource] using hY, by simpa only [hsource] using hZ, hYZ, hdeficit⟩

theorem weight_bound {s y z L : ℕ} (e B : Finset ℕ) (hcard : (e ∪ B).card = s)
    (hL : 0 < L) (heB : Disjoint e B) (hy : y ∉ e ∪ B) (hz : z ∉ e ∪ B) (hyz : y ≠ z)
    (hzero : runRelativeNullity L (TwoTargetFamilyCover.family B (y, z)) = 0)
    (hproper : ∀ C : Finset ℕ, C ⊂ TwoTargetFamilyCover.family B (y, z) →
      Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) C)) :
    infiniteJointMoment L (TwoTargetFamilyCover.family (e ∪ B) (y, z)) ≤
      (infiniteJointMoment L e * ∏ x ∈ B, infiniteMarginal x L) *
        (infiniteMarginal y L * infiniteMarginal z L *
          (2 ^ Module.finrank F₂ (Kernel y z L (sourceSpace (e ∪ B) L)) : ℝ)) := by
  have hEA : Disjoint e (TwoTargetFamilyCover.family B (y, z)) := by
    apply disjoint_left.mpr
    intro x hx hA
    change x ∈ insert y (insert z B) at hA
    rcases mem_insert.mp hA with rfl | hA
    · exact hy (mem_union_left _ hx)
    · rcases mem_insert.mp hA with rfl | hxB
      · exact hz (mem_union_left _ hx)
      · exact disjoint_left.mp heB hx hxB
  have hdata := (data e B hcard hy hz hyz hzero hproper).2.2.2
  calc
    _ = infiniteJointMoment L (e ∪ TwoTargetFamilyCover.family B (y, z)) :=
      congrArg (infiniteJointMoment L) (union_family e B (y, z)).symm
    _ ≤ infiniteJointMoment L e *
        ((∏ x ∈ TwoTargetFamilyCover.family B (y, z), infiniteMarginal x L) *
          (2 ^ MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) e)
            (fun x ↦ squareClassSpace x L) (TwoTargetFamilyCover.family B (y, z)) : ℝ)) :=
      ExtensionJointFactor.upper_bound L hL e _ hEA
    _ = _ := by
      rw [hdata]
      change infiniteJointMoment L e * ((∏ x ∈ insert y (insert z B), infiniteMarginal x L) * _) = _
      rw [prod_insert (by
        simp only [mem_insert, not_or]
        exact ⟨hyz, fun h ↦ hy (mem_union_right _ h)⟩),
        prod_insert (fun h ↦ hz (mem_union_right _ h))]
      ring

end PaperP1.DirectCrossingTargets
