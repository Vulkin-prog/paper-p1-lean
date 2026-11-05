module

public import PaperP1.Model.PositiveJointRestriction
public import PaperP1.Model.ThirdRunActivityComparison

/-! # Exact positive-marginal restriction of filtered activities and repeated-index cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FilteredPositiveRestriction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositiveMarginalRestriction
  PaperP1.TripleActivityConnected PaperP1.ThirdRunFactorialCumulant

theorem sum_restrict (G : Finset ℕ) (L r : ℕ) (P : Finset ℕ → Prop)
    (f : ℝ → ℝ) (hf : f 0 = 0) [DecidablePred P] :
    (∑ I ∈ (G.powersetCard r).filter P, f (infiniteCenteredCoefficient L I)) =
      ∑ I ∈ ((positiveGround G L).powersetCard r).filter P,
        f (infiniteCenteredCoefficient L I) := by
  classical
  symm
  have hsub : ((positiveGround G L).powersetCard r).filter P ⊆ (G.powersetCard r).filter P := by
    intro I hI
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hI).1
    exact mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨hIG.trans (positiveGround_subset G L), hcard⟩, (mem_filter.mp hI).2⟩
  apply sum_subset hsub
  intro I hI hnot
  obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hI).1
  have hnosub : ¬ I ⊆ positiveGround G L := fun h ↦
    hnot (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨h, hcard⟩, (mem_filter.mp hI).2⟩)
  obtain ⟨x, hxI, hxnot⟩ := not_subset.mp hnosub
  have hnpos : ¬ 0 < infiniteMarginal x L := fun h ↦ hxnot (mem_filter.mpr ⟨hIG hxI, h⟩)
  have hp : infiniteMarginal x L = 0 := le_antisymm (le_of_not_gt hnpos)
    (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  rw [zero_centered L I x hxI hp, hf]

theorem incompatible_restrict (G : Finset ℕ) (L r : ℕ) :
    CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard r) =
      CompatibleActivitySplit.incompatibleAbsolute L ((positiveGround G L).powersetCard r) := by
  classical
  exact sum_restrict G L r (fun I ↦ infiniteJointMoment L I = 0) abs (by simp)

theorem positive_connected_restrict (G : Finset ℕ) (L r : ℕ) :
    positiveConnected L (G.powersetCard r) =
      positiveConnected L ((positiveGround G L).powersetCard r) := by
  classical
  exact sum_restrict G L r (fun I ↦ ConnectedWindowFamilies.Connected L I ∧
    0 < infiniteJointMoment L I) id rfl

theorem repeated_cost_restrict {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G =
      RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L)
        (positiveGround G L) := by
  have hfull := ThirdRunActivityComparison.exact_decomposition (L := L) hG
  have hpos := ThirdRunActivityComparison.exact_decomposition (L := L) ((positiveGround_subset G L).trans hG)
  have hc := PositiveJointRestriction.third_restrict (L := L) hG
  have hs : CompatibleActivitySplit.signed L (G.powersetCard 3) =
      CompatibleActivitySplit.signed L ((positiveGround G L).powersetCard 3) :=
    PositiveMarginalRestriction.sum_restrict G L 3 id rfl
  linarith only [hfull, hpos, hc, hs]

end PaperP1.FilteredPositiveRestriction
