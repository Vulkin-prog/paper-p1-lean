module

public import PaperP1.Affine.PartitionMoments
public import PaperP1.Model.JointStartProbability

/-!
# Direct square-class partitions factor actual finite run moments

The square-class/character equivalence transports the relation-restriction
criterion. Both actual joint and centered finite-cylinder moments then factor
by the proved effective-space moment identities.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Model

local instance startPartitionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem relationDirect_squareClass_to_rows (M L : ℕ) (g : ι → ℕ) (hcut : ∀ i, g i + L ≤ M)
    (P : Finpartition (Finset.univ : Finset ι))
    (hP : RelationDirectPartition (squareClassFamilySpace L g) P) :
    RelationDirectPartition (startFamilySpace M L g) P := by
  intro r hr C hC
  let s := (squareClassFamilyEquivRow M L g hcut).symm r
  have he : squareClassFamilyEquivRow M L g hcut s = r :=
    (squareClassFamilyEquivRow M L g hcut).apply_symm_apply r
  have hs : relationAddition (squareClassFamilySpace L g) s = 0 := by
    apply (squareClassFamily_relation_zero_iff M L g hcut s).mp
    rwa [he]
  have hsC := hP s hs C hC
  rw [← he]
  simp only [squareClassFamilyEquivRow_apply]
  rw [← map_sum, hsC, map_zero]

omit [DecidableEq ι] in
theorem startFamilyJointMoment_eq_effective (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L)) :
    startFamilyJointMoment M L g =
      effectiveJointMoment (startFamilySpace M L g) (startFamilyWitness M L g hc) := by
  unfold startFamilyJointMoment effectiveJointMoment cylinderProbability
  congr 1
  funext ω
  apply Finset.prod_congr rfl
  intro i _
  exact startIndicator_eq_effective M L g hL hc i ω

theorem startFamilyJointMoment_partition (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L))
    (P : Finpartition (Finset.univ : Finset ι))
    (hP : RelationDirectPartition (startFamilySpace M L g) P) :
    startFamilyJointMoment M L g = ∏ C : P.parts,
      startFamilyJointMoment M L (fun i : C.val => g i.val) := by
  rw [startFamilyJointMoment_eq_effective M L g hL hc,
    effectiveJointMoment_partition _ P hP]
  apply Finset.prod_congr rfl
  intro C _
  symm
  exact startFamilyJointMoment_eq_effective M L (fun i : C.val => g i.val) hL (fun i => hc i.val)

theorem startFamilyCenteredMoment_partition (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hc : ∀ i, Compatible (startSystem M (g i) L) (startRhs L))
    (P : Finpartition (Finset.univ : Finset ι))
    (hP : RelationDirectPartition (startFamilySpace M L g) P) :
    startFamilyCenteredMoment M L g = ∏ C : P.parts,
      startFamilyCenteredMoment M L (fun i : C.val => g i.val) := by
  rw [startFamilyCenteredMoment_eq_effective M L g hL hc,
    effectiveCenteredMoment_partition _ P hP]
  apply Finset.prod_congr rfl
  intro C _
  symm
  exact startFamilyCenteredMoment_eq_effective M L (fun i : C.val => g i.val) hL (fun i => hc i.val)

end PaperP1.Model
