module

public import PaperP1.Model.InfiniteTripleCancellation

/-! # Every heterogeneous triple joint moment is its centered activity plus pair terms and its independent product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleJointReconstruction

open Finset PaperP1.Algebra PaperP1.Model.InfiniteStarts

theorem identity (L : ℕ) (T : Finset ℕ) (hT : T.card = 3) :
    infiniteJointMoment L T = infiniteCenteredCoefficient L T +
      (∑ z ∈ T, infiniteCenteredCoefficient L (T.erase z) * infiniteMarginal z L) +
      ∏ z ∈ T, infiniteMarginal z L := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hT
  have hpair (a b : ℕ) (hab : a ≠ b) :
      infiniteCenteredCoefficient L {a, b} = infiniteJointMoment L {a, b} -
        infiniteMarginal a L * infiniteMarginal b L :=
    (InfiniteTripleCancellation.coefficient_eq_transform L {a, b}).trans
      (centeredCoefficient_pair_eq_covariance _ _ hab (infiniteJointMoment_empty L)
        (InfiniteTripleCancellation.singleton_joint L a) (InfiniteTripleCancellation.singleton_joint L b))
  have hnorm := InfiniteTripleCancellation.normalized L hxy hxz hyz
  simp [hxy, hxz, hyz, erase_insert_of_ne hxy, erase_insert_of_ne hxz, erase_insert_of_ne hyz,
    hpair x y hxy, hpair x z hxz, hpair y z hyz]
  linarith only [hnorm]

theorem absolute_bound (L : ℕ) (T : Finset ℕ) (hT : T.card = 3) :
    infiniteJointMoment L T ≤ |infiniteCenteredCoefficient L T| +
      (∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
      ∏ z ∈ T, infiniteMarginal z L := by
  rw [identity L T hT]
  apply add_le_add _ le_rfl
  apply add_le_add (le_abs_self _)
  apply sum_le_sum
  intro z _
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (MissingBlockProbabilities.infiniteMarginal_nonneg z L)

theorem error_bound (L : ℕ) (T : Finset ℕ) (hT : T.card = 3) :
    |infiniteJointMoment L T - infiniteCenteredCoefficient L T| ≤
      (∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) +
      ∏ z ∈ T, infiniteMarginal z L := by
  have heq : infiniteJointMoment L T - infiniteCenteredCoefficient L T =
      (∑ z ∈ T, infiniteCenteredCoefficient L (T.erase z) * infiniteMarginal z L) +
      ∏ z ∈ T, infiniteMarginal z L := by rw [identity L T hT]; ring
  rw [heq]
  calc
    _ ≤ |∑ z ∈ T, infiniteCenteredCoefficient L (T.erase z) * infiniteMarginal z L| +
        |∏ z ∈ T, infiniteMarginal z L| := abs_add_le _ _
    _ ≤ (∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z) * infiniteMarginal z L|) +
        ∏ z ∈ T, infiniteMarginal z L := by
      rw [abs_of_nonneg (prod_nonneg fun z _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg z L)]
      exact add_le_add (abs_sum_le_sum_abs _ _) le_rfl
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro z _
      rw [abs_mul, abs_of_nonneg (MissingBlockProbabilities.infiniteMarginal_nonneg z L)]

end PaperP1.TripleJointReconstruction
