module

public import PaperP1.Model.DependentFamilySeeds
public import PaperP1.Affine.RetainedNullity

/-! # A three-element family either has a pairwise isolated vertex or at least two dependent pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TriplePairDependence

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

theorem isolated_or_two (L : ℕ) (T : Finset ℕ) (hT : T.card = 3) :
    (∃ x ∈ T, ∀ y ∈ T.erase x, Disjoint (squareClassSpace x L) (squareClassSpace y L)) ∨
      2 ≤ (DependentFamilySeeds.dependentFamilies T L 2).card := by
  classical
  by_cases hiso : ∃ x ∈ T, ∀ y ∈ T.erase x,
      Disjoint (squareClassSpace x L) (squareClassSpace y L)
  · exact Or.inl hiso
  right
  let D := DependentFamilySeeds.dependentFamilies T L 2
  have hcover : T ⊆ D.biUnion id := by
    intro x hx
    have hn : ¬ ∀ y ∈ T.erase x, Disjoint (squareClassSpace x L) (squareClassSpace y L) :=
      fun h ↦ hiso ⟨x, hx, h⟩
    push Not at hn
    obtain ⟨y, hy, hnd⟩ := hn
    have hxy : x ≠ y := (mem_erase.mp hy).1.symm
    have hdep : 0 < runRelativeNullity L {x, y} := by
      rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ _ _ hxy]
      apply Nat.pos_of_ne_zero
      intro hz
      exact hnd (disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hz))
    have he : ({x, y} : Finset ℕ) ∈ D := mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hx, (mem_erase.mp hy).2⟩,
        card_pair hxy⟩, hdep⟩
    exact mem_biUnion.mpr ⟨{x, y}, he, mem_insert_self _ _⟩
  have hsum : (∑ e ∈ D, e.card) = 2 * D.card := by
    have heq : (∑ e ∈ D, e.card) = ∑ _e ∈ D, 2 := by
      apply sum_congr rfl
      intro e he
      exact (mem_powersetCard.mp (mem_filter.mp he).1).2
    rw [heq, sum_const, smul_eq_mul]
    omega
  have hle := (card_le_card hcover).trans (card_biUnion_le (s := D) (t := id))
  change T.card ≤ ∑ e ∈ D, e.card at hle
  rw [hsum] at hle
  change 2 ≤ D.card
  omega

end PaperP1.TriplePairDependence
