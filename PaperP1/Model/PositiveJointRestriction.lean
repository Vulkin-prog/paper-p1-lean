module

public import PaperP1.Model.PositiveMarginalRestriction
public import PaperP1.Model.ThirdRunFactorialCumulant

/-! # Removing zero-marginal sites preserves all actual factorial moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveJointRestriction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositiveMarginalRestriction
  PaperP1.FactorialCountMoments PaperP1.ThirdRunFactorialCumulant

local instance positiveJointRestrictionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem joint_zero (L : ℕ) (I : Finset ℕ) (x : ℕ) (hx : x ∈ I)
    (hp : infiniteMarginal x L = 0) : infiniteJointMoment L I = 0 := by
  apply le_antisymm _ (infiniteJointMoment_nonneg L I)
  have h := MissingBlockProbabilities.infiniteJointMoment_antitone L (singleton_subset_iff.mpr hx)
  simpa only [InfiniteTripleCancellation.singleton_joint, hp] using h

theorem sum_restrict (G : Finset ℕ) (L r : ℕ) :
    (∑ I ∈ G.powersetCard r, infiniteJointMoment L I) =
      ∑ I ∈ (positiveGround G L).powersetCard r, infiniteJointMoment L I := by
  symm
  have hsub : (positiveGround G L).powersetCard r ⊆ G.powersetCard r := by
    intro I hI
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp hI
    exact mem_powersetCard.mpr ⟨hIG.trans (positiveGround_subset G L), hcard⟩
  apply sum_subset hsub
  intro I hI hnot
  obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp hI
  have hnosub : ¬ I ⊆ positiveGround G L := fun h ↦ hnot (mem_powersetCard.mpr ⟨h, hcard⟩)
  obtain ⟨x, hxI, hxnot⟩ := not_subset.mp hnosub
  have hnpos : ¬ 0 < infiniteMarginal x L := fun h ↦ hxnot (mem_filter.mpr ⟨hIG hxI, h⟩)
  exact joint_zero L I x hxI (le_antisymm (le_of_not_gt hnpos) (MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem factorial_restrict {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    factorialCountMoment G L r = factorialCountMoment (positiveGround G L) L r := by
  rw [factorialCountMoment_eq_subset hG,
    factorialCountMoment_eq_subset ((positiveGround_subset G L).trans hG), sum_restrict]

theorem third_restrict {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    thirdFactorialCumulant G L = thirdFactorialCumulant (positiveGround G L) L := by
  simp only [thirdFactorialCumulant, factorial_restrict hG]

end PaperP1.PositiveJointRestriction
