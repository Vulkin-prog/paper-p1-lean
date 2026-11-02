module

public import PaperP1.Model.CompatibleRunCentered

/-! # Exact positive/zero-mass activity decomposition at every fixed or finite order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompatibleActivitySplit

open Finset PaperP1.Model.InfiniteStarts

local instance compatibleActivitySplitDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def absolute (L : ℕ) (F : Finset (Finset ℕ)) : ℝ := ∑ I ∈ F, |infiniteCenteredCoefficient L I|

def signed (L : ℕ) (F : Finset (Finset ℕ)) : ℝ := ∑ I ∈ F, infiniteCenteredCoefficient L I

def positive (L : ℕ) (F : Finset (Finset ℕ)) : ℝ :=
  ∑ I ∈ F.filter (fun I ↦ 0 < infiniteJointMoment L I), infiniteCenteredCoefficient L I

def incompatibleAbsolute (L : ℕ) (F : Finset (Finset ℕ)) : ℝ :=
  ∑ I ∈ F.filter (fun I ↦ infiniteJointMoment L I = 0), |infiniteCenteredCoefficient L I|

def incompatibleSigned (L : ℕ) (F : Finset (Finset ℕ)) : ℝ :=
  ∑ I ∈ F.filter (fun I ↦ infiniteJointMoment L I = 0), infiniteCenteredCoefficient L I

theorem absolute_split (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ)) :
    absolute L F = positive L F + incompatibleAbsolute L F := by
  unfold absolute positive incompatibleAbsolute
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro I _
  by_cases hq : 0 < infiniteJointMoment L I
  · have hz : infiniteJointMoment L I ≠ 0 := ne_of_gt hq
    simp only [hq, hz, ite_true, ite_false, add_zero,
      abs_of_nonneg (CompatibleRunCentered.coefficient_nonneg L I hL hq)]
  · have hz : infiniteJointMoment L I = 0 := le_antisymm (le_of_not_gt hq) (infiniteJointMoment_nonneg L I)
    rw [ite_eq_right hq, ite_eq_left hz, zero_add]

theorem signed_split (L : ℕ) (F : Finset (Finset ℕ)) :
    signed L F = positive L F + incompatibleSigned L F := by
  unfold signed positive incompatibleSigned
  rw [sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro I _
  by_cases hq : 0 < infiniteJointMoment L I
  · have hz : infiniteJointMoment L I ≠ 0 := ne_of_gt hq
    simp only [hq, hz, ite_true, ite_false, add_zero]
  · have hz : infiniteJointMoment L I = 0 := le_antisymm (le_of_not_gt hq) (infiniteJointMoment_nonneg L I)
    rw [ite_eq_right hq, ite_eq_left hz, zero_add]

theorem positive_nonneg (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ)) : 0 ≤ positive L F :=
  sum_nonneg fun I hI ↦ CompatibleRunCentered.coefficient_nonneg L I hL (mem_filter.mp hI).2

theorem absolute_minus_positive (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ)) :
    absolute L F - positive L F = incompatibleAbsolute L F := by
  rw [absolute_split L hL F, add_sub_cancel_left]

theorem absolute_minus_positive_nonneg (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ)) :
    0 ≤ absolute L F - positive L F := by
  rw [absolute_minus_positive L hL F]
  exact sum_nonneg fun _ _ ↦ abs_nonneg _

theorem signed_error (L : ℕ) (F : Finset (Finset ℕ)) :
    |signed L F - positive L F| ≤ incompatibleAbsolute L F := by
  rw [signed_split L F, add_sub_cancel_left]
  exact abs_sum_le_sum_abs _ _

end PaperP1.CompatibleActivitySplit
