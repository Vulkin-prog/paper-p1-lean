module

public import PaperP1.Model.BlockJointIntersection
public import PaperP1.Model.DependentFamilySeeds

/-! # Actual four-window seeds made from two disjoint dependent pairs of small span intersection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowTwoPairSeeds

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank

def sourcePairs (G : Finset ℕ) (L : ℕ) (a : ℝ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  let P := DependentFamilySeeds.dependentFamilies G L 2
  exact (P ×ˢ P).filter fun p ↦ Disjoint p.1 p.2 ∧
    (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) p.1 ⊓
      span (fun x ↦ squareClassSpace x L) p.2) : ℝ) ≤ a * L

def families (G : Finset ℕ) (L : ℕ) (a : ℝ) : Finset (Finset ℕ) :=
  (sourcePairs G L a).image fun p ↦ p.1 ∪ p.2

theorem mem_sourcePairs (G : Finset ℕ) (L : ℕ) (a : ℝ) (p : Finset ℕ × Finset ℕ) :
    p ∈ sourcePairs G L a ↔
      p.1 ∈ DependentFamilySeeds.dependentFamilies G L 2 ∧
      p.2 ∈ DependentFamilySeeds.dependentFamilies G L 2 ∧ Disjoint p.1 p.2 ∧
      (Module.finrank F₂ ↥(span (fun x ↦ squareClassSpace x L) p.1 ⊓
        span (fun x ↦ squareClassSpace x L) p.2) : ℝ) ≤ a * L := by
  classical
  simp only [sourcePairs, mem_filter, mem_product]
  tauto

theorem family_data (G : Finset ℕ) (L : ℕ) (a : ℝ) (I : Finset ℕ) (hI : I ∈ families G L a) :
    I ⊆ G ∧ I.card = 4 ∧ ∃ p ∈ sourcePairs G L a, p.1 ∪ p.2 = I := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hI
  obtain ⟨he, hf, hdis, _hsmall⟩ := (mem_sourcePairs G L a p).mp hp
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (mem_filter.mp he).1
  obtain ⟨hfG, hfcard⟩ := mem_powersetCard.mp (mem_filter.mp hf).1
  exact ⟨union_subset heG hfG, by rw [card_union_of_disjoint hdis, hecard, hfcard], p, hp, rfl⟩

theorem mass_bound (G : Finset ℕ) (L : ℕ) (a : ℝ) :
    (∑ I ∈ families G L a, infiniteJointMoment L I) ≤
      ∑ p ∈ sourcePairs G L a, infiniteJointMoment L (p.1 ∪ p.2) :=
  sum_image_le_of_nonneg (fun I _ ↦ infiniteJointMoment_nonneg L I)

end PaperP1.LowTwoPairSeeds
