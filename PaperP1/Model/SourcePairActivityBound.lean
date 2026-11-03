module

public import PaperP1.Model.NonalignedActivityHostCap
public import PaperP1.Model.SourcePairPositiveWeight
public import PaperP1.Model.PairLossWeights

/-! # A finite full-source-rank majorant for every actual nonaligned covariance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePairActivityBound

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedPairRankLoss
  PaperP1.NonalignedActivityHostCap

theorem weighted_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) ≤
      (2 * ((2 ^ L : ℝ)⁻¹) ^ 2) *
        (∑ p ∈ sources N L, SourcePairPositiveWeight.weight p.1 p.2 L) +
          PairHostIndependentMass.mass N L := by
  classical
  have hcover := ActivityFamilyCover.two_families L (AllAlignedPairs.nonaligned N L)
    ((sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ))) ∅
    (fun _ he hn ↦ mem_union_left _ (nonzero_cover hN hL he hn))
  simp only [CompatibleActivitySplit.absolute, sum_empty, add_zero] at hcover
  calc
    _ ≤ ∑ e ∈ (sources N L).image (fun p : ℕ × ℕ ↦ ({p.1, p.2} : Finset ℕ)),
        |infiniteCenteredCoefficient L e| := hcover
    _ ≤ ∑ p ∈ sources N L, |infiniteCenteredCoefficient L {p.1, p.2}| :=
      sum_image_le_of_nonneg (f := fun e : Finset ℕ ↦ |infiniteCenteredCoefficient L e|)
        (fun _ _ ↦ abs_nonneg _)
    _ ≤ ∑ p ∈ sources N L,
        ((2 * ((2 ^ L : ℝ)⁻¹) ^ 2) * SourcePairPositiveWeight.weight p.1 p.2 L +
          infiniteMarginal p.1 L * infiniteMarginal p.2 L) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpHost, hxy, _hnon⟩ := mem_filter.mp hp
      obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hpHost).1
      have hxpos : 0 < p.1 := by have h := (mem_Ico.mp hx).1; omega
      have hypos : 0 < p.2 := by have h := (mem_Ico.mp hy).1; omega
      have hloss : 1 ≤ pairLoss p.1 p.2 L := (mem_filter.mp hpHost).2
      have htwo : (2 : ℝ) ≤ 2 ^ pairLoss p.1 p.2 L := by
        simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hloss
      have hq : infiniteJointMoment L {p.1, p.2} ≤
          (2 * ((2 ^ L : ℝ)⁻¹) ^ 2) * SourcePairPositiveWeight.weight p.1 p.2 L := by
        apply (PairLossWeights.joint_bound hxpos hypos hL).trans
        unfold SourcePairPositiveWeight.weight
        nlinarith only [htwo, sq_nonneg ((2 ^ L : ℝ)⁻¹)]
      have hq0 := infiniteJointMoment_nonneg L {p.1, p.2}
      have hprod := mul_nonneg (HeterogeneousRunConversion.marginal_bounds p.1 L).1
        (HeterogeneousRunConversion.marginal_bounds p.2 L).1
      rw [CompressedJointMoments.centered_pair L _ (card_pair_eq_two_iff.mpr hxy.ne), prod_pair hxy.ne]
      have habs := abs_sub_le (infiniteJointMoment L {p.1, p.2}) 0
        (infiniteMarginal p.1 L * infiniteMarginal p.2 L)
      simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hq0, abs_of_nonneg hprod] at habs
      exact habs.trans (add_le_add hq le_rfl)
    _ = (2 * ((2 ^ L : ℝ)⁻¹) ^ 2) *
        (∑ p ∈ sources N L, SourcePairPositiveWeight.weight p.1 p.2 L) +
        ∑ p ∈ sources N L, infiniteMarginal p.1 L * infiniteMarginal p.2 L := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p _ _ ↦ mul_nonneg (HeterogeneousRunConversion.marginal_bounds p.1 L).1
        (HeterogeneousRunConversion.marginal_bounds p.2 L).1))

end PaperP1.SourcePairActivityBound
