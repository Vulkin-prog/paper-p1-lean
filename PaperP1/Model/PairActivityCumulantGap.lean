module

public import PaperP1.Model.IncompatiblePairActivity
public import PaperP1.Model.HeterogeneousRunConversion

/-! # Exact nonnegative gap between absolute pair activity and half the second cumulant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairActivityCumulantGap

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem exact_gap {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (hL : 0 < L) :
    CompatibleActivitySplit.absolute L (G.powersetCard 2) -
      RegularCumulantTransfer.secondFactorialCumulant G L / 2 =
        2 * CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 2) +
          (∑ x ∈ G, infiniteMarginal x L ^ 2) / 2 := by
  have hcum := HeterogeneousRunConversion.second_cumulant_formula (L := L) hG
  change RegularCumulantTransfer.secondFactorialCumulant G L =
    2 * CompatibleActivitySplit.signed L (G.powersetCard 2) - ∑ x ∈ G, infiniteMarginal x L ^ 2 at hcum
  have hgap := IncompatiblePairActivity.signed_absolute_gap G L hL
  linarith only [hcum, hgap]

end PaperP1.PairActivityCumulantGap
