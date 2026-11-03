module

public import PaperP1.Model.GoodApartPairProducts
public import PaperP1.Combinatorics.BadPairProductCover

/-! # Exact finite reduction of the remaining apart cost to the actual channel partition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonDirectApartPartition

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteGoodChannelPartition PaperP1.DirectPairProductComparison

theorem bad_activity (Q N H L : ℕ) (hL : 0 < L) :
    (∑ e ∈ (dyadicBlock N).powersetCard 2 \ good Q N H L, |infiniteCenteredCoefficient L e|) =
      CompatibleActivitySplit.absolute L (weak Q N H L) +
        CompatibleActivitySplit.absolute L (exceptional Q N H L) := by
  classical
  have hsub : good Q N H L ⊆ (dyadicBlock N).powersetCard 2 :=
    fun e he ↦ (mem_filter.mp (good_subset Q N H L he)).1
  have hsum := sum_sdiff hsub (f := fun e ↦ |infiniteCenteredCoefficient L e|)
  have hsplit := activity_decomposition Q N H L hL
  unfold CompatibleActivitySplit.absolute at hsplit ⊢
  linarith only [hsum, hsplit]

theorem finite_bound (Q N H L : ℕ) (hL : 0 < L) :
    nonDirectApartCost (dyadicBlock N) L ≤
      CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) *
        (CompatibleActivitySplit.absolute L (weak Q N H L) +
          CompatibleActivitySplit.absolute L (exceptional Q N H L)) +
      GoodApartPairProducts.mass Q N H L := by
  classical
  have hb := BadPairProductCover.bad_bound ((dyadicBlock N).powersetCard 2) (good Q N H L)
    (nonDirectApartPairs (dyadicBlock N) L) (filter_subset _ _)
    (fun e ↦ |infiniteCenteredCoefficient L e|) (fun e ↦ abs_nonneg _)
  rw [bad_activity Q N H L hL] at hb
  have hs := sum_filter_add_sum_filter_not (nonDirectApartPairs (dyadicBlock N) L)
    (fun S ↦ S ⊆ good Q N H L) (fun S ↦ ∏ e ∈ S, |infiniteCenteredCoefficient L e|)
  change GoodApartPairProducts.mass Q N H L + _ = nonDirectApartCost (dyadicBlock N) L at hs
  change _ ≤ CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) * _ at hb
  linarith only [hb, hs]

end PaperP1.NonDirectApartPartition
