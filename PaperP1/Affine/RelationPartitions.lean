module

public import PaperP1.Affine.Relations
public import Mathlib.Order.Partition.Finpartition

/-!
# Partitions preserved by every effective relation

A partition respects relations when every zero-sum tuple still has zero sum
after restriction to each part. Such partitions are closed under common
refinement and have a unique finest member. Equivalence with directness of
the block-sum subspaces and probability factorization are separate steps.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance relationPartitionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance relationPartitionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U)

def restrictCoefficients (C : Finset ι) : ((i : ι) → S i) →ₗ[𝔽₂] ((i : ι) → S i) where
  toFun := fun s i => if i ∈ C then s i else 0
  map_add' := by intro s t; funext i; by_cases hi : i ∈ C <;> simp [hi]
  map_smul' := by intro a s; funext i; by_cases hi : i ∈ C <;> simp [hi]

theorem relationAddition_restrictCoefficients (C : Finset ι) (s : (i : ι) → S i) :
    relationAddition S (restrictCoefficients S C s) = ∑ i ∈ C, (s i).val := by
  simp only [relationAddition_apply, restrictCoefficients, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [apply_ite, ZeroMemClass.coe_zero]
  rw [← Finset.sum_filter]
  simp

omit [Fintype ι] in
theorem sum_restrictCoefficients (C D : Finset ι) (s : (i : ι) → S i) :
    (∑ i ∈ D, (restrictCoefficients S C s i).val) = ∑ i ∈ C ∩ D, (s i).val := by
  simp only [restrictCoefficients, LinearMap.coe_mk, AddHom.coe_mk, apply_ite,
    ZeroMemClass.coe_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp [and_comm]

/-- A global effective relation restricts to a relation on every part. -/
def RelationDirectPartition (P : Finpartition (Finset.univ : Finset ι)) : Prop :=
  ∀ s : (i : ι) → S i, relationAddition S s = 0 →
    ∀ C ∈ P.parts, ∑ i ∈ C, (s i).val = 0

theorem relationDirectPartition_top : RelationDirectPartition S ⊤ := by
  intro s hs C hC
  have hCeq : C = Finset.univ :=
    Finset.mem_singleton.mp (Finpartition.parts_top_subset _ hC)
  subst C
  exact hs

theorem relationDirectPartition_inf {P Q : Finpartition (Finset.univ : Finset ι)}
    (hP : RelationDirectPartition S P) (hQ : RelationDirectPartition S Q) :
    RelationDirectPartition S (P ⊓ Q) := by
  intro s hs C hC
  rw [Finpartition.parts_inf] at hC
  obtain ⟨⟨D, E⟩, hDE, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hC)
  obtain ⟨hD, hE⟩ := Finset.mem_product.mp hDE
  have hsumD : relationAddition S (restrictCoefficients S D s) = 0 := by
    rw [relationAddition_restrictCoefficients]
    exact hP s hs D hD
  have hsumE := hQ (restrictCoefficients S D s) hsumD E hE
  simpa only [sum_restrictCoefficients, Finset.inf_eq_inter] using hsumE

theorem relationDirectPartition_finsetInf
    (F : Finset (Finpartition (Finset.univ : Finset ι)))
    (hF : ∀ P ∈ F, RelationDirectPartition S P) :
    RelationDirectPartition S (F.inf id) := by
  induction F using Finset.induction_on with
  | empty => exact relationDirectPartition_top S
  | @insert P F hPF ih =>
    rw [Finset.inf_insert]
    exact relationDirectPartition_inf S (hF P (Finset.mem_insert_self _ _))
      (ih (fun Q hQ => hF Q (Finset.mem_insert_of_mem hQ)))

def relationDirectPartitions : Finset (Finpartition (Finset.univ : Finset ι)) :=
  Finset.univ.filter (RelationDirectPartition S)

def canonicalRelationPartition : Finpartition (Finset.univ : Finset ι) :=
  (relationDirectPartitions S).inf id

theorem canonicalRelationPartition_respects : RelationDirectPartition S (canonicalRelationPartition S) := by
  apply relationDirectPartition_finsetInf
  intro P hP
  exact (Finset.mem_filter.mp hP).2

theorem canonicalRelationPartition_le (P : Finpartition (Finset.univ : Finset ι))
    (hP : RelationDirectPartition S P) : canonicalRelationPartition S ≤ P := by
  exact Finset.inf_le (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩)

theorem existsUnique_finest_relationPartition :
    ∃! P : Finpartition (Finset.univ : Finset ι),
      RelationDirectPartition S P ∧ ∀ Q, RelationDirectPartition S Q → P ≤ Q := by
  refine ⟨canonicalRelationPartition S,
    ⟨canonicalRelationPartition_respects S, canonicalRelationPartition_le S⟩, ?_⟩
  intro P hP
  exact le_antisymm (hP.2 _ (canonicalRelationPartition_respects S))
    (canonicalRelationPartition_le S P hP.1)

end PaperP1.Affine
