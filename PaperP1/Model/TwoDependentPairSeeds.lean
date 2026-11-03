module

public import PaperP1.Affine.RelationLossMonotonicity
public import PaperP1.Model.CoreCanonicalComponents
public import PaperP1.Model.DependentFamilySeeds

/-! # Two disjoint actual dependent pairs give a four-window seed with no singleton canonical part -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoDependentPairSeeds

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RelationProjectionRank PaperP1.RelationCoreWitnesses

def sourcePairs (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  let P := DependentFamilySeeds.dependentFamilies G L 2
  exact (P ×ˢ P).filter fun p ↦ Disjoint p.1 p.2

def families (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  (sourcePairs G L).image fun p ↦ p.1 ∪ p.2

theorem mem_sourcePairs (G : Finset ℕ) (L : ℕ) (p : Finset ℕ × Finset ℕ) :
    p ∈ sourcePairs G L ↔ p.1 ∈ DependentFamilySeeds.dependentFamilies G L 2 ∧
      p.2 ∈ DependentFamilySeeds.dependentFamilies G L 2 ∧ Disjoint p.1 p.2 := by
  classical
  simp only [sourcePairs, mem_filter, mem_product]
  tauto

theorem union_core (L : ℕ) (e f : Finset ℕ) (he : e.card = 2) (hf : f.card = 2)
    (hdepE : 0 < runRelativeNullity L e) (hdepF : 0 < runRelativeNullity L f) : Core 2 L (e ∪ f) := by
  intro x hx
  rcases mem_union.mp hx with hxe | hxf
  · have h := RelationLossMonotonicity.mono (fun x ↦ squareClassSpace x L) e (e ∪ f) subset_union_left x hxe
    rw [RelationLossMonotonicity.pair_loss _ e he x hxe] at h
    change runRelativeNullity L e ≤ loss (fun x ↦ squareClassSpace x L) (e ∪ f) x at h
    omega
  · have h := RelationLossMonotonicity.mono (fun x ↦ squareClassSpace x L) f (e ∪ f) subset_union_right x hxf
    rw [RelationLossMonotonicity.pair_loss _ f hf x hxf] at h
    change runRelativeNullity L f ≤ loss (fun x ↦ squareClassSpace x L) (e ∪ f) x at h
    omega

theorem family_data (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (hI : I ∈ families G L) :
    I ⊆ G ∧ I.card = 4 ∧ Core 2 L I := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hI
  obtain ⟨he, hf, hdis⟩ := (mem_sourcePairs G L p).mp hp
  obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (mem_filter.mp he).1
  obtain ⟨hfG, hfcard⟩ := mem_powersetCard.mp (mem_filter.mp hf).1
  exact ⟨union_subset heG hfG, by rw [card_union_of_disjoint hdis, hecard, hfcard],
    union_core L p.1 p.2 hecard hfcard (mem_filter.mp he).2 (mem_filter.mp hf).2⟩

end PaperP1.TwoDependentPairSeeds
