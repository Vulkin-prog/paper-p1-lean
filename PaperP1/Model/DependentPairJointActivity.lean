module

public import PaperP1.Model.CompatibleActivitySplit
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.DependentFamilySeeds

/-! # Every actual dependent pair joint probability is bounded by twice its absolute centered activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentPairJointActivity

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem pointwise (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (hcard : e.card = 2)
    (hdep : 0 < runRelativeNullity L e) :
    infiniteJointMoment L e ≤ 2 * |infiniteCenteredCoefficient L e| := by
  by_cases hq : 0 < infiniteJointMoment L e
  · have hqeq := infiniteJointMoment_exact_of_pos (e.sup fun x ↦ x + L) L e hL
      (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq
    have hpow : (2 : ℝ) ≤ 2 ^ runRelativeNullity L e := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdep
    have hprod : 0 ≤ ∏ x ∈ e, infiniteMarginal x L :=
      prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
    have hmul := mul_le_mul_of_nonneg_left hpow hprod
    have hcent := CompressedJointMoments.centered_pair L e hcard
    change infiniteJointMoment L e = (∏ x ∈ e, infiniteMarginal x L) * (2 ^ runRelativeNullity L e : ℝ) at hqeq
    have h := le_abs_self (infiniteCenteredCoefficient L e)
    nlinarith only [hqeq, hmul, hcent, h]
  · exact (le_of_not_gt hq).trans (mul_nonneg (by norm_num) (abs_nonneg _))

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    (∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, infiniteJointMoment L e) ≤
      2 * CompatibleActivitySplit.absolute L (G.powersetCard 2) := by
  classical
  calc
    _ ≤ ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, 2 * |infiniteCenteredCoefficient L e| := by
      apply sum_le_sum
      intro e he
      obtain ⟨heG, hdep⟩ := mem_filter.mp he
      exact pointwise L hL e (mem_powersetCard.mp heG).2 hdep
    _ = 2 * ∑ e ∈ DependentFamilySeeds.dependentFamilies G L 2, |infiniteCenteredCoefficient L e| := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e _ _ ↦ abs_nonneg _)) (by norm_num)

end PaperP1.DependentPairJointActivity
