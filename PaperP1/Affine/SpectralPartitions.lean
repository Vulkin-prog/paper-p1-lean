module

public import PaperP1.Affine.DirectPartitions

/-!
# Factorization of finite spectra over direct partitions

An arbitrary local frequency condition handles both centered spectra, where
zero frequencies are excluded, and ordinary affine spectra, where they are
allowed. Directness splits the global relation condition into the conditions
inside each part.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance spectralPartitionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance spectralPartitionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂))
variable (P : Finpartition (Finset.univ : Finset ι))

def HasFrequencyRelation (T : (i : ι) → S i → Prop) (s : (i : ι) → S i) : Prop :=
  (∀ i, T i (s i)) ∧ relationAddition S s = 0

theorem group_frequency_conditions_iff (T : (i : ι) → S i → Prop) (s : (i : ι) → S i) :
    (∀ i, T i (s i)) ↔ ∀ C : P.parts, ∀ i : C.val, T i.val (groupCoefficients S P s C i) := by
  constructor
  · intro h C i
    exact h i.val
  · intro h i
    exact h ⟨P.part i, P.part_mem.mpr (Finset.mem_univ i)⟩ ⟨i, P.mem_part (Finset.mem_univ i)⟩

theorem group_relation_zero_iff (hP : RelationDirectPartition S P) (s : (i : ι) → S i) :
    relationAddition S s = 0 ↔ ∀ C : P.parts,
      relationAddition (fun i : C.val => S i.val) (groupCoefficients S P s C) = 0 := by
  constructor
  · intro hs C
    exact (groupCoefficients_part_sum S P s C).trans (hP s hs C.val C.property)
  · intro h
    exact (groupCoefficients_total_sum S P s).symm.trans (Finset.sum_eq_zero fun C _ => h C)

theorem frequencyRelation_group_iff (hP : RelationDirectPartition S P)
    (T : (i : ι) → S i → Prop) (s : (i : ι) → S i) :
    HasFrequencyRelation S T s ↔ ∀ C : P.parts,
      HasFrequencyRelation (fun i : C.val => S i.val) (fun i => T i.val)
        (groupCoefficients S P s C) := by
  rw [HasFrequencyRelation, group_frequency_conditions_iff S P,
    group_relation_zero_iff S P hP]
  simp only [HasFrequencyRelation, forall_and]

theorem affineTupleSign_partition (a : ι → V) (s : (i : ι) → S i) :
    affineTupleSign S a s = ∏ C : P.parts,
      affineTupleSign (fun i : C.val => S i.val) (fun i => a i.val) (groupCoefficients S P s C) := by
  have hC (C : P.parts) :
      affineTupleSign (fun i : C.val => S i.val) (fun i => a i.val) (groupCoefficients S P s C) =
        ∏ i ∈ C.val, realCharacter (s i).val (a i) := by
    change (∏ i : C.val, realCharacter (s i.val).val (a i.val)) = _
    rw [Finset.univ_eq_attach]
    exact Finset.prod_attach C.val (fun i => realCharacter (s i).val (a i))
  simp_rw [hC]
  exact (partition_prod P (fun i => realCharacter (s i).val (a i))).symm

theorem prod_frequency_terms (hP : RelationDirectPartition S P) (a : ι → V)
    (T : (i : ι) → S i → Prop) (s : (i : ι) → S i) :
    (∏ C : P.parts,
      if HasFrequencyRelation (fun i : C.val => S i.val) (fun i => T i.val)
          (groupCoefficients S P s C) then
        affineTupleSign (fun i : C.val => S i.val) (fun i => a i.val)
          (groupCoefficients S P s C) else 0) =
      if HasFrequencyRelation S T s then affineTupleSign S a s else 0 := by
  by_cases h : ∀ C : P.parts, HasFrequencyRelation (fun i : C.val => S i.val)
      (fun i => T i.val) (groupCoefficients S P s C)
  · rw [ite_eq_left ((frequencyRelation_group_iff S P hP T s).mpr h)]
    simp_rw [ite_eq_left (h _)]
    exact (affineTupleSign_partition S P a s).symm
  · rw [ite_eq_right (mt (frequencyRelation_group_iff S P hP T s).mp h)]
    obtain ⟨C, hC⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ C) (ite_eq_right hC)

variable [∀ i, Fintype (S i)]

def spectralCoefficient (a : ι → V) (T : (i : ι) → S i → Prop) : ℝ :=
  ∑ s : (i : ι) → S i, if HasFrequencyRelation S T s then affineTupleSign S a s else 0

theorem spectralCoefficient_partition (hP : RelationDirectPartition S P) (a : ι → V)
    (T : (i : ι) → S i → Prop) :
    spectralCoefficient S a T = ∏ C : P.parts,
      spectralCoefficient (fun i : C.val => S i.val) (fun i => a i.val) (fun i => T i.val) := by
  unfold spectralCoefficient
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (groupCoefficientsEquiv S P).toEquiv
  intro s
  exact (prod_frequency_terms S P hP a T s).symm

end PaperP1.Affine
