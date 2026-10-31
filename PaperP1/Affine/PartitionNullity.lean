module

public import PaperP1.Affine.DirectPartitions

/-!
# Relation-kernel splitting and nullity additivity

For a direct partition, regrouping the coefficients identifies the global
relation kernel with the product of the relation kernels inside each part.
Taking dimensions gives exact additivity of effective relative nullity.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance partitionNullityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) (P : Finpartition (Finset.univ : Finset ι))

def groupRelationKernel (hP : RelationDirectPartition S P) :
    LinearMap.ker (relationAddition S) →ₗ[𝔽₂]
      ((C : P.parts) → LinearMap.ker (relationAddition (fun i : C.val => S i.val))) where
  toFun := fun s C => ⟨groupCoefficients S P s.val C,
    (groupCoefficients_part_sum S P s.val C).trans (hP s.val s.property C.val C.property)⟩
  map_add' := by intro s t; funext C; apply Subtype.ext; rfl
  map_smul' := by intro a s; funext C; apply Subtype.ext; rfl

def ungroupRelationKernel :
    ((C : P.parts) → LinearMap.ker (relationAddition (fun i : C.val => S i.val))) →ₗ[𝔽₂]
      LinearMap.ker (relationAddition S) where
  toFun := fun w => ⟨ungroupCoefficients S P (fun C => (w C).val), by
    have hs := groupCoefficients_total_sum S P
      (ungroupCoefficients S P (fun C => (w C).val))
    rw [group_ungroupCoefficients] at hs
    exact hs.symm.trans (Finset.sum_eq_zero fun C _ => (w C).property)⟩
  map_add' := by intro s t; apply Subtype.ext; rfl
  map_smul' := by intro a s; apply Subtype.ext; rfl

theorem groupRelationKernel_injective (hP : RelationDirectPartition S P) :
    Function.Injective (groupRelationKernel S P hP) := by
  intro s t h
  apply Subtype.ext
  apply (groupCoefficientsEquiv S P).injective
  funext C
  exact congrArg Subtype.val (congrFun h C)

theorem groupRelationKernel_surjective (hP : RelationDirectPartition S P) :
    Function.Surjective (groupRelationKernel S P hP) := by
  intro w
  refine ⟨ungroupRelationKernel S P w, ?_⟩
  funext C
  apply Subtype.ext
  exact congrFun (group_ungroupCoefficients S P (fun C => (w C).val)) C

def relationKernelPartitionEquiv (hP : RelationDirectPartition S P) :
    LinearMap.ker (relationAddition S) ≃ₗ[𝔽₂]
      ((C : P.parts) → LinearMap.ker (relationAddition (fun i : C.val => S i.val))) :=
  LinearEquiv.ofBijective (groupRelationKernel S P hP)
    ⟨groupRelationKernel_injective S P hP, groupRelationKernel_surjective S P hP⟩

variable [∀ i, Fintype (S i)]

theorem relativeNullity_partition_additive (hP : RelationDirectPartition S P) :
    relativeNullity S = ∑ C : P.parts, relativeNullity (fun i : C.val => S i.val) := by
  classical
  let : ∀ C : P.parts, AddCommGroup (LinearMap.ker (relationAddition (fun i : C.val => S i.val))) :=
    fun C => Submodule.addCommGroup (R := 𝔽₂) (M := (i : C.val) → S i.val) _
  let : ∀ C : P.parts, Module.Free 𝔽₂ (LinearMap.ker (relationAddition (fun i : C.val => S i.val))) :=
    fun C => Module.Free.of_divisionRing 𝔽₂ (LinearMap.ker (relationAddition (fun i : C.val => S i.val)))
  have h := (relationKernelPartitionEquiv S P hP).finrank_eq
  rw [Module.finrank_pi_fintype] at h
  exact h

theorem relativeNullity_canonical_additive :
    relativeNullity S = ∑ C : (canonicalRelationPartition S).parts,
      relativeNullity (fun i : C.val => S i.val) :=
  relativeNullity_partition_additive S _ (canonicalRelationPartition_respects S)

end PaperP1.Affine
