module

public import PaperP1.Affine.PartitionGrouping
public import PaperP1.Affine.RelativeNullity

/-!
# Direct partitions of actual block-sum subspaces

The relation-restriction criterion is equivalent to injectivity of addition
from the sum-spaces of the parts. This identifies the previously constructed
finest partition with the canonical direct decomposition in the manuscript.
Probability and nullity factorization are developed separately.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance directPartitionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) (P : Finpartition (Finset.univ : Finset ι))

/-- The actual sum of the effective subspaces in one partition part. -/
def blockSpace (C : Finset ι) : Submodule 𝔽₂ U :=
  LinearMap.range (relationAddition (fun i : C => S i.val))

omit [Fintype ι] [DecidableEq ι] in
theorem blockSpace_eq_iSup (C : Finset ι) : blockSpace S C = ⨆ i : C, S i.val :=
  range_relationAddition _

abbrev blockFamily (C : P.parts) : Submodule 𝔽₂ U := blockSpace S C.val

/-- A zero sum of vectors in the part-spaces has every component zero. -/
def BlockDirectPartition : Prop :=
  ∀ z : (C : P.parts) → blockFamily S P C,
    relationAddition (blockFamily S P) z = 0 → ∀ C, z C = 0

def blockTotals : ((i : ι) → S i) →ₗ[𝔽₂] ((C : P.parts) → blockFamily S P C) where
  toFun := fun s C => (relationAddition (fun i : C.val => S i.val)).rangeRestrict
    (groupCoefficients S P s C)
  map_add' := by
    intro s t
    funext C
    apply Subtype.ext
    change relationAddition (fun i : C.val => S i.val)
        ((groupCoefficients S P s C) + (groupCoefficients S P t C)) = _
    exact map_add _ _ _
  map_smul' := by
    intro a s
    funext C
    apply Subtype.ext
    change relationAddition (fun i : C.val => S i.val) (a • groupCoefficients S P s C) = _
    exact map_smul _ _ _

@[simp]
theorem blockTotals_apply (s : (i : ι) → S i) (C : P.parts) :
    (blockTotals S P s C).val =
      relationAddition (fun i : C.val => S i.val) (groupCoefficients S P s C) := rfl

theorem blockTotals_total_sum (s : (i : ι) → S i) :
    relationAddition (blockFamily S P) (blockTotals S P s) = relationAddition S s := by
  exact groupCoefficients_total_sum S P s

theorem blockTotals_surjective : Function.Surjective (blockTotals S P) := by
  intro z
  have h : ∀ C : P.parts, ∃ w : (i : C.val) → S i.val,
      relationAddition (fun i : C.val => S i.val) w = (z C).val := fun C => (z C).property
  choose w hw using h
  refine ⟨ungroupCoefficients S P w, ?_⟩
  funext C
  apply Subtype.ext
  change relationAddition (fun i : C.val => S i.val)
    (groupCoefficients S P (ungroupCoefficients S P w) C) = (z C).val
  rw [group_ungroupCoefficients]
  exact hw C

theorem relationDirect_iff_blockDirect : RelationDirectPartition S P ↔ BlockDirectPartition S P := by
  constructor
  · intro hP z hz C
    obtain ⟨s, rfl⟩ := blockTotals_surjective S P z
    have hs : relationAddition S s = 0 := by rwa [blockTotals_total_sum] at hz
    apply Subtype.ext
    change relationAddition (fun i : C.val => S i.val) (groupCoefficients S P s C) = 0
    rw [groupCoefficients_part_sum]
    exact hP s hs C.val C.property
  · intro hP s hs C hC
    have hz : relationAddition (blockFamily S P) (blockTotals S P s) = 0 := by
      rw [blockTotals_total_sum, hs]
    have hCzero := congrArg Subtype.val (hP (blockTotals S P s) hz (⟨C, hC⟩ : P.parts))
    change relationAddition (fun i : C => S i.val)
      (groupCoefficients S P s (⟨C, hC⟩ : P.parts)) = 0 at hCzero
    exact (groupCoefficients_part_sum S P s (⟨C, hC⟩ : P.parts)).symm.trans hCzero

theorem blockDirect_iff_addition_injective :
    BlockDirectPartition S P ↔ Function.Injective (relationAddition (blockFamily S P)) := by
  constructor
  · intro hP z w hzw
    have hz : relationAddition (blockFamily S P) (z - w) = 0 := by
      rw [map_sub, hzw, sub_self]
    funext C
    exact sub_eq_zero.mp (hP (z - w) hz C)
  · intro hinj z hz C
    have hzero : z = 0 := hinj (hz.trans (map_zero _).symm)
    rw [hzero]
    rfl

theorem canonicalRelationPartition_direct : BlockDirectPartition S (canonicalRelationPartition S) :=
  (relationDirect_iff_blockDirect S _).mp (canonicalRelationPartition_respects S)

theorem canonicalRelationPartition_le_direct (hP : BlockDirectPartition S P) :
    canonicalRelationPartition S ≤ P :=
  canonicalRelationPartition_le S P ((relationDirect_iff_blockDirect S P).mpr hP)

theorem existsUnique_finest_directPartition :
    ∃! P : Finpartition (Finset.univ : Finset ι),
      BlockDirectPartition S P ∧ ∀ Q, BlockDirectPartition S Q → P ≤ Q := by
  refine ⟨canonicalRelationPartition S,
    ⟨canonicalRelationPartition_direct S, fun Q => canonicalRelationPartition_le_direct S Q⟩, ?_⟩
  intro Q hQ
  exact le_antisymm (hQ.2 _ (canonicalRelationPartition_direct S))
    (canonicalRelationPartition_le_direct S Q hQ.1)

end PaperP1.Affine
