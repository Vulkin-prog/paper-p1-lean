module

public import PaperP1.Model.AllAlignedPairs
public import PaperP1.Model.HeterogeneousRunConversion

/-! # Exact original second-cumulant split with a literal nonaligned remainder -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedCumulantReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem signed_partition (N L : ℕ) :
    CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L) +
      CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) =
        CompatibleActivitySplit.signed L ((dyadicBlock N).powersetCard 2) :=
  sum_sdiff (f := infiniteCenteredCoefficient L) (filter_subset _ _)

theorem second_cumulant_split (N L : ℕ) (b : ℝ) :
    RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 2 * b =
      2 * CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L) +
      2 * (CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - b) -
        ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 := by
  have hcum := HeterogeneousRunConversion.second_cumulant_formula (L := L) (subset_refl (dyadicBlock N))
  change RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L =
    2 * CompatibleActivitySplit.signed L ((dyadicBlock N).powersetCard 2) - ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 at hcum
  have hs := signed_partition N L
  linarith only [hcum, hs]

theorem finite_bound (N L : ℕ) (b : ℝ) :
    |RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 2 * b| ≤
      2 * CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
      2 * |CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - b| +
        ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 := by
  rw [second_cumulant_split]
  have hdiag : 0 ≤ ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hnon : |CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L)| ≤
      CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) := abs_sum_le_sum_abs _ _
  calc
    _ ≤ |2 * CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L) +
        2 * (CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - b)| +
        |∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2| := abs_sub _ _
    _ ≤ (|2 * CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L)| +
        |2 * (CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - b)|) +
        |∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2| := by
      have hh := abs_add_le
        (2 * CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L))
        (2 * (CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - b))
      linarith only [hh]
    _ = 2 * |CompatibleActivitySplit.signed L (AllAlignedPairs.nonaligned N L)| +
        2 * |CompatibleActivitySplit.signed L (AllAlignedPairs.families N L) - b| +
        ∑ x ∈ dyadicBlock N, infiniteMarginal x L ^ 2 := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num, abs_of_nonneg hdiag]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hnon (by norm_num : (0 : ℝ) ≤ 2)
      linarith only [hh]

end PaperP1.AlignedCumulantReduction
