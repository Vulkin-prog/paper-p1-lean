module

public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Model.PositiveMarginalRestriction
public import PaperP1.Algebra.CenteredCardConvolution
public import PaperP1.Algebra.ElementarySymmetricBound

/-! # An actual fixed-order absolute activity bound from dependent joint and product mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AbsoluteActivityDecomposition

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.DependentFamilySeeds PaperP1.HeterogeneousDirectMaximum

local instance absoluteActivityDecompositionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem centered_zero_direct (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hne : I.Nonempty)
    (hzero : runRelativeNullity L I = 0) : infiniteCenteredCoefficient L I = 0 := by
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · exact CompressedJointMoments.centered_zero_of_no_full_support L hL I hp
      (CompressedRelationSupport.no_full_support_of_nullity_zero _ I hne hzero)
  · push Not at hp
    obtain ⟨x, hx, hp⟩ := hp
    exact PositiveMarginalRestriction.zero_centered L I x hx
      (le_antisymm hp (MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem absolute_eq_dependent (G : Finset ℕ) (L r : ℕ) (hL : 0 < L) (hr : 1 ≤ r) :
    (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) =
      ∑ I ∈ dependentFamilies G L r, |infiniteCenteredCoefficient L I| := by
  symm
  apply sum_subset (filter_subset _ _)
  intro I hI hnot
  have hz : runRelativeNullity L I = 0 := by
    by_contra hn
    exact hnot (mem_filter.mpr ⟨hI, Nat.pos_of_ne_zero hn⟩)
  have hne : I.Nonempty := card_pos.mp (by have h := (mem_powersetCard.mp hI).2; omega)
  rw [centered_zero_direct L hL I hne hz, abs_zero]

theorem centered_bound (L : ℕ) (I : Finset ℕ) :
    |infiniteCenteredCoefficient L I| ≤ ∑ A ∈ I.powerset,
      infiniteJointMoment L A * ∏ x ∈ I \ A, infiniteMarginal x L := by
  rw [InfiniteTripleCancellation.coefficient_eq_transform]
  unfold centeredCoefficient
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro A _
  have hq := infiniteJointMoment_nonneg L A
  have hp : 0 ≤ ∏ x ∈ I \ A, infiniteMarginal x L :=
    prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg hq, abs_of_nonneg hp, le_refl]

theorem centered_split (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    |infiniteCenteredCoefficient L I| ≤ (2 : ℝ) ^ I.card * (∏ x ∈ I, infiniteMarginal x L) +
      ∑ A ∈ I.powerset, (if 0 < runRelativeNullity L A then infiniteJointMoment L A else 0) *
        ∏ x ∈ I \ A, infiniteMarginal x L := by
  have hprod : 0 ≤ ∏ x ∈ I, infiniteMarginal x L :=
    prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  calc
    _ ≤ ∑ A ∈ I.powerset, infiniteJointMoment L A * ∏ x ∈ I \ A, infiniteMarginal x L := centered_bound L I
    _ ≤ ∑ A ∈ I.powerset, ((∏ x ∈ I, infiniteMarginal x L) +
        (if 0 < runRelativeNullity L A then infiniteJointMoment L A else 0) *
          ∏ x ∈ I \ A, infiniteMarginal x L) := by
      apply sum_le_sum
      intro A hA
      by_cases hz : runRelativeNullity L A = 0
      · rw [direct_joint_factor L hL A hz, hz]
        simp only [lt_self_iff_false, ite_false, zero_mul, add_zero]
        rw [mul_comm, prod_sdiff (mem_powerset.mp hA)]
      · rw [ite_eq_left (Nat.pos_of_ne_zero hz)]
        exact le_add_of_nonneg_left hprod
    _ = _ := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]

theorem absolute_elementary_bound (G : Finset ℕ) (L r : ℕ) (hL : 0 < L) (hr : 1 ≤ r) :
    (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤
      (2 : ℝ) ^ r * (∑ I ∈ dependentFamilies G L r, ∏ x ∈ I, infiniteMarginal x L) +
      ∑ s ∈ range (r + 1), ∑ A ∈ dependentFamilies G L s,
        infiniteJointMoment L A * SubsetPowerSums.elementary (fun x ↦ infiniteMarginal x L) (G \ A) (r - s) := by
  let d := fun A ↦ if 0 < runRelativeNullity L A then infiniteJointMoment L A else 0
  let Q := fun I : Finset ℕ ↦ ∑ A ∈ I.powerset, d A * ∏ x ∈ I \ A, infiniteMarginal x L
  have hQ (I : Finset ℕ) : 0 ≤ Q I := by
    apply sum_nonneg
    intro A _
    apply mul_nonneg
    · dsimp [d]; split_ifs
      · exact infiniteJointMoment_nonneg L A
      · exact le_rfl
    · exact prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  rw [absolute_eq_dependent G L r hL hr]
  calc
    _ ≤ ∑ I ∈ dependentFamilies G L r, ((2 : ℝ) ^ r * (∏ x ∈ I, infiniteMarginal x L) + Q I) := by
      apply sum_le_sum
      intro I hI
      have hc := (mem_powersetCard.mp (mem_filter.mp hI).1).2
      simpa only [hc] using centered_split L hL I
    _ = (2 : ℝ) ^ r * (∑ I ∈ dependentFamilies G L r, ∏ x ∈ I, infiniteMarginal x L) +
        ∑ I ∈ dependentFamilies G L r, Q I := by rw [sum_add_distrib, mul_sum]
    _ ≤ (2 : ℝ) ^ r * (∑ I ∈ dependentFamilies G L r, ∏ x ∈ I, infiniteMarginal x L) +
        ∑ I ∈ G.powersetCard r, Q I :=
      add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun I _ _ ↦ hQ I))
    _ = _ := by
      congr 1
      rw [CenteredCardConvolution.convolution G (fun x ↦ infiniteMarginal x L) Q d (fun _ _ ↦ rfl) r]
      apply sum_congr rfl
      intro s _
      change (∑ A ∈ G.powersetCard s, (if 0 < runRelativeNullity L A then infiniteJointMoment L A else 0) * _) = _
      simp only [ite_mul, zero_mul]
      rw [← sum_filter]
      rfl

theorem absolute_power_bound (G : Finset ℕ) (L r : ℕ) (hL : 0 < L) (hr : 1 ≤ r) :
    (∑ I ∈ G.powersetCard r, |infiniteCenteredCoefficient L I|) ≤
      (2 : ℝ) ^ r * (∑ I ∈ dependentFamilies G L r, ∏ x ∈ I, infiniteMarginal x L) +
      ∑ s ∈ range (r + 1), dependentMass G L s *
        (actualMean G L ^ (r - s) / ((r - s).factorial : ℝ)) := by
  apply (absolute_elementary_bound G L r hL hr).trans
  apply add_le_add le_rfl
  apply sum_le_sum
  intro s _
  calc
    _ ≤ ∑ A ∈ dependentFamilies G L s, infiniteJointMoment L A *
        (actualMean G L ^ (r - s) / ((r - s).factorial : ℝ)) := by
      apply sum_le_sum
      intro A _
      apply mul_le_mul_of_nonneg_left _ (infiniteJointMoment_nonneg L A)
      exact (ElementarySymmetricBound.elementary_le_power_div (fun x ↦ infiniteMarginal x L)
        (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) (G \ A) (r - s)).trans
          (div_le_div_of_nonneg_right (pow_le_pow_left₀
            (sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
            (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))
            (r - s)) (Nat.cast_nonneg _))
    _ = _ := (sum_mul _ _ _).symm

end PaperP1.AbsoluteActivityDecomposition
