module

public import PaperP1.Model.FourthDirectPairSum
public import PaperP1.Model.FourthRunRemainder

/-! # The actual connected fourth cumulant reduced to the remaining disjoint non-direct cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedFourthReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FourthRunFactorialCumulant
  PaperP1.DirectPairProductComparison

theorem exact_reduction (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    fourthFactorialCumulant G L -
      24 * CompatibleActivitySplit.signed L (ConnectedWindowFamilies.connectedFamilies G L 4) =
    FourthRunRemainder.remainder G L -
      24 * (CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2 / 2 - signedDirect G L) := by
  rw [FourthRunRemainder.remainder, FourthDirectPairSum.quartic_split G L hL]
  ring

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    |fourthFactorialCumulant G L -
      24 * CompatibleActivitySplit.signed L (ConnectedWindowFamilies.connectedFamilies G L 4)| ≤
    |FourthRunRemainder.remainder G L| +
      12 * (PairRowActivity.repeatedSquare G L + PairRowActivity.starSquare G L) +
      24 * nonDirectApartCost G L := by
  rw [exact_reduction G L hL]
  have ht := abs_sub (FourthRunRemainder.remainder G L)
    (24 * (CompatibleActivitySplit.signed L (G.powersetCard 2) ^ 2 / 2 - signedDirect G L))
  rw [abs_mul] at ht
  rw [show |(24 : ℝ)| = 24 by norm_num] at ht
  have hp := DirectPairProductComparison.finite_bound G L
  linarith only [ht, hp]

end PaperP1.ConnectedFourthReduction
