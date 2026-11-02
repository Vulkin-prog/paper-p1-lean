module

public import PaperP1.Model.CompatibleActivitySplit

/-! # The nonnegative absolute-minus-signed activity gap is monotone in the family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActivitySignGap

open Finset PaperP1.Model.InfiniteStarts

theorem nonneg (L : ℕ) (F : Finset (Finset ℕ)) :
    0 ≤ CompatibleActivitySplit.absolute L F - CompatibleActivitySplit.signed L F :=
  sub_nonneg.mpr (sum_le_sum fun _ _ ↦ le_abs_self _)

theorem mono (L : ℕ) {F G : Finset (Finset ℕ)} (hFG : F ⊆ G) :
    CompatibleActivitySplit.absolute L F - CompatibleActivitySplit.signed L F ≤
      CompatibleActivitySplit.absolute L G - CompatibleActivitySplit.signed L G := by
  calc
    _ = ∑ e ∈ F, (|infiniteCenteredCoefficient L e| - infiniteCenteredCoefficient L e) := (sum_sub_distrib (s := F) (fun e ↦ |infiniteCenteredCoefficient L e|) (fun e ↦ infiniteCenteredCoefficient L e)).symm
    _ ≤ ∑ e ∈ G, (|infiniteCenteredCoefficient L e| - infiniteCenteredCoefficient L e) :=
      sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ ↦ sub_nonneg.mpr (le_abs_self _))
    _ = _ := sum_sub_distrib (s := G) (fun e ↦ |infiniteCenteredCoefficient L e|) (fun e ↦ infiniteCenteredCoefficient L e)

end PaperP1.ActivitySignGap
