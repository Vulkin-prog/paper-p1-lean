module

public import PaperP1.Model.DirectPairProductComparison

/-! # A coarse unconditional bound on the literal remaining disjoint pair cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectPairCostBound

open Finset PaperP1.Model.InfiniteStarts PaperP1.DirectPairProductComparison

theorem finite_bound (G : Finset ℕ) (L : ℕ) :
    nonDirectApartCost G L ≤ CompatibleActivitySplit.absolute L (G.powersetCard 2) ^ 2 / 2 := by
  classical
  calc
    _ ≤ ∑ S ∈ (G.powersetCard 2).powersetCard 2, ∏ e ∈ S, |infiniteCenteredCoefficient L e| :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun S _ _ ↦ prod_nonneg fun e _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))
    _ ≤ _ := ElementarySymmetricBound.elementary_le_power_div
      (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)
      (G.powersetCard 2) 2

end PaperP1.DirectPairCostBound
