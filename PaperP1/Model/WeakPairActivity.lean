module

public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Model.PairRowActivity

/-! # Literal weak and incompatible dependent pairs with exact heterogeneous weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakPairActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DependentFamilySeeds

def Weak (L : ℕ) (η : ℝ) (I : Finset ℕ) : Prop :=
  (runRelativeNullity L I : ℝ) ≤ η * L ∨ infiniteJointMoment L I = 0

def pairs (G : Finset ℕ) (L : ℕ) (η : ℝ) : Finset (Finset ℕ) := by
  classical
  exact (dependentFamilies G L 2).filter (Weak L η)

theorem coefficient_bound (L : ℕ) (hL : 0 < L) (η : ℝ) (hη : 0 ≤ η)
    (I : Finset ℕ) (hI : I.card = 2) (hw : Weak L η I) :
    |infiniteCenteredCoefficient L I| ≤
      2 * (2 : ℝ) ^ (η * L) * ∏ x ∈ I, infiniteMarginal x L := by
  let T := (2 : ℝ) ^ (η * L)
  let P := ∏ x ∈ I, infiniteMarginal x L
  have hP : 0 ≤ P := prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hT : 1 ≤ T := Real.one_le_rpow (by norm_num) (mul_nonneg hη (Nat.cast_nonneg L))
  have hpT : P ≤ P * T := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hP
  by_cases hq0 : infiniteJointMoment L I = 0
  · rw [CompressedJointMoments.centered_pair L I hI, hq0, zero_sub, abs_neg, abs_of_nonneg hP]
    change P ≤ 2 * T * P
    nlinarith only [hpT, hP]
  · have hq : 0 < infiniteJointMoment L I := lt_of_le_of_ne (infiniteJointMoment_nonneg L I) (Ne.symm hq0)
    have hlow : (runRelativeNullity L I : ℝ) ≤ η * L := hw.resolve_right hq0
    have hpow : (2 ^ runRelativeNullity L I : ℝ) ≤ T := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlow
    let M := I.sup fun x ↦ x + L
    have hexact : infiniteJointMoment L I = P * (2 ^ runRelativeNullity L I : ℝ) :=
      infiniteJointMoment_exact_of_pos M L I hL (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq
    have hqT : infiniteJointMoment L I ≤ P * T := by
      rw [hexact]
      exact mul_le_mul_of_nonneg_left hpow hP
    have habs : |infiniteCenteredCoefficient L I| ≤ infiniteJointMoment L I + P := by
      rw [CompressedJointMoments.centered_pair L I hI]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hq.le, abs_of_nonneg hP])
    change _ ≤ 2 * T * P
    nlinarith only [habs, hqT, hpT]

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (η : ℝ) (hη : 0 ≤ η) :
    CompatibleActivitySplit.absolute L (pairs G L η) ≤
      (2 * (2 : ℝ) ^ (η * L)) *
        ∑ I ∈ dependentFamilies G L 2, ∏ x ∈ I, infiniteMarginal x L := by
  classical
  calc
    _ ≤ ∑ I ∈ pairs G L η, (2 * (2 : ℝ) ^ (η * L)) * ∏ x ∈ I, infiniteMarginal x L := by
      apply sum_le_sum
      intro I hI
      obtain ⟨hdep, hw⟩ := mem_filter.mp hI
      exact coefficient_bound L hL η hη I (mem_powersetCard.mp (mem_filter.mp hdep).1).2 hw
    _ = (2 * (2 : ℝ) ^ (η * L)) *
        ∑ I ∈ pairs G L η, ∏ x ∈ I, infiniteMarginal x L := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun I _ _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))
      (by positivity)

end PaperP1.WeakPairActivity
