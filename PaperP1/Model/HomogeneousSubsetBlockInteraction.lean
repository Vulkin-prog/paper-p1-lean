module

public import PaperP1.Model.HomogeneousBlockIntersection
public import PaperP1.Arithmetic.SubsetEvenLoss

/-! # Actual two-block interactions are bounded by the prescribed-subset loss

No ambient ghost value is inserted into either effective block. All finite
homogeneous formulas retain incompatible original affine configurations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSubsetBlockInteraction

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.HomogeneousRunMass PaperP1.SubspaceFamilyRank

theorem actual_eq (L : ℕ) (hL : 0 < L) (E : Finset ℕ) (hq : 0 < infiniteJointMoment L E) :
    infiniteJointMoment L E = probability L E := by
  let x := FiniteFamilyEnumeration.centres E rfl
  have hs : FiniteFamilyEnumeration.tupleSet x = E := FiniteFamilyEnumeration.centres_tupleSet E rfl
  have hqtuple : 0 < PrescribedTupleMass.joint L (fun _ ↦ startRhs L) x := by
    rwa [JointTupleSupport.prescribed_eq_support x hL, hs]
  rcases PrescribedTupleRank.joint_zero_or_rank (fun _ ↦ startRhs L) x with hz | heq
  · rw [hz] at hqtuple
    exact False.elim (lt_irrefl 0 hqtuple)
  · rw [← hs, ← JointTupleSupport.prescribed_eq_support x hL, ← tuple_probability, tuple_rank]
    exact heq

theorem upper_loss (L H : ℕ) (E A U V : Finset ℕ)
    (hE : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U)
    (hA : span (fun x ↦ squareClassSpace x L) A = FiniteEvenSquareClasses.space V) :
    probability L (E ∪ A) ≤ probability L E * probability L A * (2 ^ SubsetEvenLoss.loss H U V : ℝ) := by
  rw [HomogeneousBlockIntersection.exact L E A, hE, hA]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (SubsetEvenLoss.intersection_le_loss H U V))
    (mul_nonneg (probability_pos L E).le (probability_pos L A).le)

theorem excess_upper (L H : ℕ) (E A U V : Finset ℕ)
    (hE : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U)
    (hA : span (fun x ↦ squareClassSpace x L) A = FiniteEvenSquareClasses.space V) :
    probability L (E ∪ A) - probability L E * probability L A ≤
      (probability L E * probability L A) * ((2 ^ SubsetEvenLoss.loss H U V : ℝ) - 1) := by
  have hh := upper_loss L H E A U V hE hA
  nlinarith only [hh]

theorem actual_joint_upper (L H : ℕ) (hL : 0 < L) (E A U V : Finset ℕ)
    (hE : span (fun x ↦ squareClassSpace x L) E = FiniteEvenSquareClasses.space U)
    (hA : span (fun x ↦ squareClassSpace x L) A = FiniteEvenSquareClasses.space V) :
    infiniteJointMoment L (E ∪ A) ≤ probability L E * probability L A * (2 ^ SubsetEvenLoss.loss H U V : ℝ) :=
  (HomogeneousRunMass.actual_joint_le L hL (E ∪ A)).trans (upper_loss L H E A U V hE hA)

end PaperP1.HomogeneousSubsetBlockInteraction
