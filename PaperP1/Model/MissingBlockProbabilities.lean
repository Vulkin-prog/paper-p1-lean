module

public import PaperP1.Affine.MissingBlockRelations
public import PaperP1.Model.InfiniteJointMoments
public import PaperP1.Model.RegularStarts
public import PaperP1.Probability.FiniteCoupling

/-! # The missing-block probability inequality with every exact marginal

Incompatibility is retained. The general inequality uses the actual p_x;
the regular-set version factors out the common nominal marginal 2^(-L).
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MissingBlockProbabilities

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Probability PaperP1.Algebra RegularStarts Finset

local instance missingBlockProbabilityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem infiniteMarginal_nonneg (x L : ℕ) : 0 ≤ infiniteMarginal x L := by
  rw [infiniteMarginal_eq_finite (M := x + L) le_rfl]
  exact exactMarginal_nonneg _ _ _

theorem infiniteJointMoment_antitone (L : ℕ) {I J : Finset ℕ} (hIJ : I ⊆ J) :
    infiniteJointMoment L J ≤ infiniteJointMoment L I := by
  let M := J.sup (fun x ↦ x + L)
  have hcut : ∀ x ∈ J, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
  rw [infiniteJointMoment_eq_finite M L J hcut,
    infiniteJointMoment_eq_finite M L I (fun x hx ↦ hcut x (hIJ hx))]
  unfold finiteJointMoment
  apply finiteExpectation_mono
  intro σ
  rw [indicator_product_eq_indicator, indicator_product_eq_indicator]
  by_cases hJ : ∀ x ∈ J, startIndicator x L σ = true
  · have hI : ∀ x ∈ I, startIndicator x L σ = true := fun x hx ↦ hJ x (hIJ hx)
    rw [ite_eq_left hJ, ite_eq_left hI]
  · simp only [hJ, ↓reduceIte]
    split_ifs <;> norm_num

theorem infinite_joint_missing_block_bound (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hmiss : ¬∃ w, IsFullSupportRelation (fun x : I ↦ squareClassSpace x.val L) w) :
    infiniteJointMoment L I ≤
      ∑ x ∈ I, infiniteMarginal x L * infiniteJointMoment L (I.erase x) := by
  classical
  have hright : 0 ≤ ∑ x ∈ I, infiniteMarginal x L * infiniteJointMoment L (I.erase x) :=
    sum_nonneg fun x _ ↦ mul_nonneg (infiniteMarginal_nonneg x L)
      (infiniteJointMoment_nonneg L _)
  by_cases hq : 0 < infiniteJointMoment L I
  · let M := I.sup (fun x ↦ x + L)
    have hcut : ∀ x ∈ I, x + L ≤ M := fun x hx ↦ le_sup (f := fun x ↦ x + L) hx
    have hformula (A : Finset ℕ) (hA : A ⊆ I) (hqA : 0 < infiniteJointMoment L A) :
        infiniteJointMoment L A = (∏ x ∈ A, infiniteMarginal x L) *
          (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) A : ℝ) :=
      infiniteJointMoment_exact_of_pos M L A hL (fun x hx ↦ hcut x (hA hx)) hqA
    have hterm (x : ℕ) (hx : x ∈ I) :
        infiniteMarginal x L * infiniteJointMoment L (I.erase x) =
          (∏ y ∈ I, infiniteMarginal y L) *
            (2 ^ relativeNullityOn (fun y ↦ squareClassSpace y L) (I.erase x) : ℝ) := by
      have hqerase : 0 < infiniteJointMoment L (I.erase x) :=
        hq.trans_le (infiniteJointMoment_antitone L (erase_subset x I))
      rw [hformula _ (erase_subset x I) hqerase]
      have hprod : infiniteMarginal x L * (∏ y ∈ I.erase x, infiniteMarginal y L) =
          ∏ y ∈ I, infiniteMarginal y L := by
        rw [mul_comm, prod_erase_mul _ _ hx]
      rw [← mul_assoc, hprod]
    calc
      _ = (∏ x ∈ I, infiniteMarginal x L) *
          (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) :=
        hformula I (subset_refl _) hq
      _ ≤ (∏ x ∈ I, infiniteMarginal x L) *
          ∑ x ∈ I, (2 ^ relativeNullityOn (fun y ↦ squareClassSpace y L) (I.erase x) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (missing_full_support_nullity_bound_real (fun x ↦ squareClassSpace x L) I hmiss)
          (prod_nonneg fun x _ ↦ infiniteMarginal_nonneg x L)
      _ = _ := by rw [mul_sum]; exact sum_congr rfl (fun x hx ↦ (hterm x hx).symm)
  · exact (le_of_not_gt hq).trans hright

theorem joint_missing_block_bound_of_marginal_le (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hmiss : ¬∃ w, IsFullSupportRelation (fun x : I ↦ squareClassSpace x.val L) w)
    (pmax : ℝ) (hpmax : ∀ x ∈ I, infiniteMarginal x L ≤ pmax) :
    infiniteJointMoment L I ≤ pmax * ∑ x ∈ I, infiniteJointMoment L (I.erase x) := by
  calc
    _ ≤ ∑ x ∈ I, infiniteMarginal x L * infiniteJointMoment L (I.erase x) :=
      infinite_joint_missing_block_bound L I hL hmiss
    _ ≤ ∑ x ∈ I, pmax * infiniteJointMoment L (I.erase x) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right (hpmax x hx) (infiniteJointMoment_nonneg L _)
    _ = _ := (mul_sum _ _ _).symm

theorem regular_joint_missing_block_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (I : Finset ℕ) (hI : I ⊆ regularStarts N L)
    (hmiss : ¬∃ w, IsFullSupportRelation (fun x : I ↦ squareClassSpace x.val L) w) :
    infiniteJointMoment L I ≤ (2 ^ L : ℝ)⁻¹ * ∑ x ∈ I, infiniteJointMoment L (I.erase x) := by
  calc
    _ ≤ ∑ x ∈ I, infiniteMarginal x L * infiniteJointMoment L (I.erase x) :=
      infinite_joint_missing_block_bound L I hL hmiss
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      have hxpos : 0 < x := by
        have := (mem_Ico.mp ((regularStarts_subset N L) (hI hx))).1
        omega
      rw [marginal_on_regular hxpos hL (hI hx)]

end PaperP1.MissingBlockProbabilities
