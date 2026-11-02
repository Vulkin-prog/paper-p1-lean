module

public import PaperP1.Probability.CenteredZeroMarginal
public import PaperP1.Model.CompressedJointMoments

/-! # Exact restriction of every actual centered activity to positive marginals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveMarginalRestriction

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

local instance positiveMarginalRestrictionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def positiveGround (G : Finset ℕ) (L : ℕ) : Finset ℕ :=
  G.filter fun x ↦ 0 < infiniteMarginal x L

theorem zero_centered (L : ℕ) (I : Finset ℕ) (x : ℕ) (hx : x ∈ I)
    (hp : infiniteMarginal x L = 0) : infiniteCenteredCoefficient L I = 0 := by
  let M := I.sup fun y ↦ y + L
  have hcut (y : ℕ) (hy : y ∈ I) : y + L ≤ M := le_sup (f := fun y ↦ y + L) hy
  have hfinite : Probability.exactMarginal (cylinderProbability M) (fun y ↦ startIndicator y L) x = 0 := by
    rw [← infiniteMarginal_eq_finite (hcut x hx), hp]
  rw [CompressedJointMoments.centered_to_finite M L I hcut]
  exact CenteredZeroMarginal.finite_centered_zero (cylinderProbability M)
    (fun y ↦ startIndicator y L) (fun y ↦ infiniteMarginal y L) I x hx hfinite hp

theorem positiveGround_subset (G : Finset ℕ) (L : ℕ) : positiveGround G L ⊆ G := filter_subset _ _

theorem marginal_positive {G : Finset ℕ} {L x : ℕ} (hx : x ∈ positiveGround G L) :
    0 < infiniteMarginal x L := (mem_filter.mp hx).2

theorem sum_restrict (G : Finset ℕ) (L r : ℕ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ I ∈ G.powersetCard r, f (infiniteCenteredCoefficient L I)) =
      ∑ I ∈ (positiveGround G L).powersetCard r, f (infiniteCenteredCoefficient L I) := by
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
  have hp : infiniteMarginal x L = 0 := le_antisymm (le_of_not_gt hnpos)
    (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  rw [zero_centered L I x hxI hp, hf]

end PaperP1.PositiveMarginalRestriction
