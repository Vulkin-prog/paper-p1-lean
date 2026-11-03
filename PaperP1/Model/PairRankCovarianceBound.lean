module

public import PaperP1.Model.PositiveMarginalRestriction
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.HeterogeneousDirectMaximum

/-! # A sharp homogeneous relation-weight bound for every actual pair covariance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairRankCovarianceBound

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

def rankWeight (L : ℕ) (e : Finset ℕ) : ℝ := (2 ^ runRelativeNullity L e : ℝ) - 1

theorem weight_nonneg (L : ℕ) (e : Finset ℕ) : 0 ≤ rankWeight L e :=
  sub_nonneg.mpr (one_le_pow₀ (by norm_num))

theorem coefficient_bound (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (he : e.card = 2) :
    |infiniteCenteredCoefficient L e| ≤ (∏ x ∈ e, infiniteMarginal x L) * rankWeight L e := by
  classical
  by_cases hp : ∀ x ∈ e, 0 < infiniteMarginal x L
  · let P := ∏ x ∈ e, infiniteMarginal x L
    have hP : 0 < P := prod_pos fun x hx ↦ hp x hx
    by_cases hq : infiniteJointMoment L e = 0
    · have hr : 0 < runRelativeNullity L e := by
        apply Nat.pos_of_ne_zero
        intro hz
        have h := HeterogeneousDirectMaximum.direct_joint_factor L hL e hz
        rw [hq] at h
        exact hP.ne' h.symm
      have hpow : (2 : ℝ) ≤ 2 ^ runRelativeNullity L e := by
        simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
      rw [CompressedJointMoments.centered_pair L e he, hq, zero_sub, abs_neg, abs_of_nonneg hP.le]
      dsimp only [rankWeight]
      nlinarith only [mul_le_mul_of_nonneg_left hpow hP.le]
    · have hqpos : 0 < infiniteJointMoment L e := lt_of_le_of_ne (infiniteJointMoment_nonneg L e) (Ne.symm hq)
      have hexact := infiniteJointMoment_exact_of_pos (e.sup fun x ↦ x + L) L e hL
        (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hqpos
      have heq : infiniteCenteredCoefficient L e = P * rankWeight L e := by
        rw [CompressedJointMoments.centered_pair L e he, hexact]
        dsimp only [P, rankWeight, runRelativeNullity]
        ring
      rw [heq, abs_of_nonneg (mul_nonneg hP.le (weight_nonneg L e))]
  · push Not at hp
    obtain ⟨x, hx, hpx⟩ := hp
    have hz : infiniteMarginal x L = 0 := le_antisymm hpx (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    rw [PositiveMarginalRestriction.zero_centered L e x hx hz, abs_zero, prod_eq_zero hx hz, zero_mul]

theorem pair_cap {N L x y : ℕ} (hL : 0 < L) (hxy : x ≠ y)
    (M : ℝ) (hx : infiniteMarginal x L ≤ M / N) (hy : infiniteMarginal y L ≤ M / N) :
    |infiniteCenteredCoefficient L {x, y}| ≤ (M / N) ^ 2 * rankWeight L {x, y} := by
  have hx0 := MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hy0 := MissingBlockProbabilities.infiniteMarginal_nonneg y L
  have hprod : infiniteMarginal x L * infiniteMarginal y L ≤ (M / N) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hx hy hy0 (hx0.trans hx)
  have h := coefficient_bound L hL {x, y} (by simp [hxy])
  rw [prod_pair hxy] at h
  exact h.trans (mul_le_mul_of_nonneg_right hprod (weight_nonneg L _))

end PaperP1.PairRankCovarianceBound
