module

public import PaperP1.Affine.SpectralPartitions
public import PaperP1.Affine.FourierBound

/-!
# Factorization of actual affine and centered moments

Uniform character orthogonality gives both ordinary and centered moments as
finite spectra. The spectral partition theorem then factors both kinds of
moments over any direct partition, without assuming block independence.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Affine

local instance partitionMomentPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance partitionMomentDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

def effectiveJointMoment [Fintype V] (a : ι → V) : ℝ :=
  finiteExpectation (uniformFiniteProbability V).weight
    (fun v => ∏ i, effectiveIndicator (S i) (a i) v)

theorem effective_joint_product (a : ι → V) (v : V) :
    (∏ i, effectiveIndicator (S i) (a i) v) = (∏ i, effectiveRate (S i)) *
      ∑ s : (i : ι) → S i, affineTupleSign S a s * realCharacter (relationAddition S s) v := by
  simp_rw [effectiveIndicator, effective_indicator_expansion]
  rw [Finset.prod_mul_distrib, Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib, realCharacter_sum, affineTupleSign,
    relationAddition_apply, effectiveRate]

variable [Fintype V]

theorem effective_joint_spectral (a : ι → V) :
    effectiveJointMoment S a = (∏ i, effectiveRate (S i)) *
      spectralCoefficient S a (fun _ _ => True) := by
  unfold effectiveJointMoment spectralCoefficient
  simp_rw [effective_joint_product]
  rw [finiteExpectation_const_mul, finiteExpectation_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [finiteExpectation_const_mul, uniform_character_expectation]
  simp only [HasFrequencyRelation]
  split_ifs <;> simp_all

theorem effective_centered_spectral (a : ι → V) :
    effectiveCenteredMoment S a = (∏ i, effectiveRate (S i)) *
      spectralCoefficient S a (fun _ s => s ≠ 0) := by
  exact effective_full_support_formula S a

theorem effectiveJointMoment_partition
    (P : Finpartition (Finset.univ : Finset ι)) (hP : RelationDirectPartition S P) (a : ι → V) :
    effectiveJointMoment S a = ∏ C : P.parts,
      effectiveJointMoment (fun i : C.val => S i.val) (fun i => a i.val) := by
  rw [effective_joint_spectral, spectralCoefficient_partition S P hP]
  simp_rw [effective_joint_spectral]
  rw [Finset.prod_mul_distrib, partition_prod_subtype P (fun i => effectiveRate (S i))]

theorem effectiveCenteredMoment_partition
    (P : Finpartition (Finset.univ : Finset ι)) (hP : RelationDirectPartition S P) (a : ι → V) :
    effectiveCenteredMoment S a = ∏ C : P.parts,
      effectiveCenteredMoment (fun i : C.val => S i.val) (fun i => a i.val) := by
  rw [effective_centered_spectral, spectralCoefficient_partition S P hP]
  simp_rw [effective_centered_spectral]
  rw [Finset.prod_mul_distrib, partition_prod_subtype P (fun i => effectiveRate (S i))]

end PaperP1.Affine
