module

public import PaperP1.Model.FinitePartMoments
public import PaperP1.Model.PositiveJointRestriction

/-! # Actual finite-set component factorization without an admissibility premise

A zero marginal kills both the whole moment and the factor of the unique
partition part containing that site. All original zero-mass cases are kept.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnrestrictedRunComponents

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

set_option maxHeartbeats 1000000 in
theorem joint_partition (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (P : Finpartition (univ : Finset I))
    (hP : RelationDirectPartition (fun i : I ↦ squareClassSpace i.val L) P) :
    infiniteJointMoment L I = ∏ C ∈ P.parts, infiniteJointMoment L (FinitePartImage.image C) := by
  classical
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · let M := I.sup fun x ↦ x + L
    have hcut (i : I) : i.val + L ≤ M := le_sup (f := fun x ↦ x + L) i.property
    calc
      _ = infiniteFamilyJointMoment L (fun i : I ↦ i.val) := infiniteJointMoment_eq_family_subtype L I
      _ = ∏ C : P.parts, infiniteFamilyJointMoment L (fun i : C.val ↦ i.val.val) :=
        infiniteFamilyJointMoment_partition M L (fun i : I ↦ i.val) hL hcut
          (fun i ↦ hp i.val i.property) P hP
      _ = ∏ C : P.parts, infiniteJointMoment L (FinitePartImage.image C.val) := by
        apply prod_congr rfl
        intro C _
        exact (FinitePartMoments.joint_image L C.val).symm
      _ = _ := prod_coe_sort P.parts (fun C : Finset I ↦ infiniteJointMoment L (FinitePartImage.image C))
  · push Not at hp
    obtain ⟨x, hx, hpx⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hpx
      (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    obtain ⟨C, hC, hiC⟩ := P.exists_mem (mem_univ (⟨x, hx⟩ : I))
    have hxC : x ∈ FinitePartImage.image C := mem_image.mpr ⟨⟨x, hx⟩, hiC, rfl⟩
    rw [PositiveJointRestriction.joint_zero L I x hx hz]
    exact (prod_eq_zero_iff.mpr ⟨C, hC, PositiveJointRestriction.joint_zero L _ x hxC hz⟩).symm

set_option maxHeartbeats 1000000 in
theorem centered_partition (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (P : Finpartition (univ : Finset I))
    (hP : RelationDirectPartition (fun i : I ↦ squareClassSpace i.val L) P) :
    infiniteCenteredCoefficient L I =
      ∏ C ∈ P.parts, infiniteCenteredCoefficient L (FinitePartImage.image C) := by
  classical
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · let M := I.sup fun x ↦ x + L
    have hcut (i : I) : i.val + L ≤ M := le_sup (f := fun x ↦ x + L) i.property
    calc
      _ = infiniteFamilyCenteredMoment L (fun i : I ↦ i.val) := infiniteCenteredCoefficient_eq_family_subtype L I
      _ = ∏ C : P.parts, infiniteFamilyCenteredMoment L (fun i : C.val ↦ i.val.val) :=
        infiniteFamilyCenteredMoment_partition M L (fun i : I ↦ i.val) hL hcut
          (fun i ↦ hp i.val i.property) P hP
      _ = ∏ C : P.parts, infiniteCenteredCoefficient L (FinitePartImage.image C.val) := by
        apply prod_congr rfl
        intro C _
        exact (FinitePartMoments.centered_image L C.val).symm
      _ = _ := prod_coe_sort P.parts (fun C : Finset I ↦ infiniteCenteredCoefficient L (FinitePartImage.image C))
  · push Not at hp
    obtain ⟨x, hx, hpx⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hpx
      (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    obtain ⟨C, hC, hiC⟩ := P.exists_mem (mem_univ (⟨x, hx⟩ : I))
    have hxC : x ∈ FinitePartImage.image C := mem_image.mpr ⟨⟨x, hx⟩, hiC, rfl⟩
    rw [PositiveMarginalRestriction.zero_centered L I x hx hz]
    exact (prod_eq_zero_iff.mpr ⟨C, hC, PositiveMarginalRestriction.zero_centered L _ x hxC hz⟩).symm

theorem nullity_partition (L : ℕ) (I : Finset ℕ) (P : Finpartition (univ : Finset I))
    (hP : RelationDirectPartition (fun i : I ↦ squareClassSpace i.val L) P) :
    runRelativeNullity L I = ∑ C ∈ P.parts, runRelativeNullity L (FinitePartImage.image C) := by
  calc
    _ = ∑ C : P.parts, relativeNullity (fun i : C.val ↦ squareClassSpace i.val.val L) :=
      relativeNullity_partition_additive (fun i : I ↦ squareClassSpace i.val L) P hP
    _ = ∑ C : P.parts, runRelativeNullity L (FinitePartImage.image C.val) := by
      apply sum_congr rfl
      intro C _
      exact FinitePartImage.nullity_image (fun x ↦ squareClassSpace x L) C.val
    _ = _ := sum_coe_sort P.parts (fun C : Finset I ↦ runRelativeNullity L (FinitePartImage.image C))

set_option maxHeartbeats 1000000 in
theorem canonical_run_components (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    ∃! P : Finpartition (univ : Finset I),
      CanonicalRunPartitionConclusion L (fun i : I ↦ i.val) P := by
  classical
  let S := fun i : I ↦ squareClassSpace i.val L
  let P := canonicalRelationPartition S
  have hrel := canonicalRelationPartition_respects S
  have hdir := canonicalRelationPartition_direct S
  refine ⟨P, ⟨hdir, ?_, ?_, ?_, relativeNullity_canonical_additive S⟩, ?_⟩
  · intro Q hQ
    exact canonicalRelationPartition_le_direct S Q hQ
  · rw [← infiniteJointMoment_eq_family_subtype]
    calc
      _ = ∏ C ∈ P.parts, infiniteJointMoment L (FinitePartImage.image C) := joint_partition L hL I P hrel
      _ = ∏ C : P.parts, infiniteJointMoment L (FinitePartImage.image C.val) :=
        (prod_coe_sort P.parts (fun C : Finset I ↦ infiniteJointMoment L (FinitePartImage.image C))).symm
      _ = _ := by
        apply prod_congr rfl
        intro C _
        exact FinitePartMoments.joint_image L C.val
  · rw [← infiniteCenteredCoefficient_eq_family_subtype]
    calc
      _ = ∏ C ∈ P.parts, infiniteCenteredCoefficient L (FinitePartImage.image C) := centered_partition L hL I P hrel
      _ = ∏ C : P.parts, infiniteCenteredCoefficient L (FinitePartImage.image C.val) :=
        (prod_coe_sort P.parts (fun C : Finset I ↦ infiniteCenteredCoefficient L (FinitePartImage.image C))).symm
      _ = _ := by
        apply prod_congr rfl
        intro C _
        exact FinitePartMoments.centered_image L C.val
  · intro Q hQ
    exact le_antisymm (hQ.2.1 P hdir) (canonicalRelationPartition_le_direct S Q hQ.1)

end PaperP1.UnrestrictedRunComponents
