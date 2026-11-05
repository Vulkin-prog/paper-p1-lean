module

public import PaperP1.Asymptotics.StrongNonalignedSourceProfile
public import PaperP1.Combinatorics.TwoEdgeTripleCover
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Main Proposition 12.2 for literal actual unordered triples

The source-pair and target populations are constructed from the actual family.
Incompatible triples are allowed as well, since their actual joint mass is zero.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongNonalignedTripleProfile

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem main_12_2
    (C θ σ ε : ℝ) (hθ : 0 < θ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ ConnectedWindowFamilies.Connected L I ∧
        (runRelativeNullity L I : ℝ) ≤ σ * L ∧
        ∃ x ∈ I, ∃ y ∈ I, x ≠ y ∧ ActualOffsetNonalignment.NoExact x y L ∧
          θ * L ≤ (FreeComponentRank.pairIntersectionRank x y L : ℝ)) →
      (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-min (3 / 2) (3 - σ) + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := StrongNonalignedSourceProfile.uniform_sources
    C θ σ ε hθ hσ hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hF
  classical
  let P := ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦ p.1 ≠ p.2 ∧
    ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
    θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ)
  let S := fun p : ℕ × ℕ ↦ (dyadicBlock N).filter fun z ↦
    z ∉ ({p.1, p.2} : Finset ℕ) ∧ insert z {p.1, p.2} ∈ F
  have hP (p : ℕ × ℕ) (hp : p ∈ P) :
      p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧
        ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
        θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ) := by
    obtain ⟨hpG, hneq, hno, hdim⟩ := mem_filter.mp hp
    exact ⟨(mem_product.mp hpG).1, (mem_product.mp hpG).2, hneq, hno, hdim⟩
  have hS (p : ℕ × ℕ) (_hp : p ∈ P) (z : ℕ) (hz : z ∈ S p) :
      z ∈ dyadicBlock N ∧ z ∉ ({p.1, p.2} : Finset ℕ) ∧
        ConnectedWindowFamilies.Connected L (insert z {p.1, p.2}) ∧
        (runRelativeNullity L (insert z {p.1, p.2}) : ℝ) ≤ σ * L := by
    obtain ⟨hzG, hfresh, hfamily⟩ := mem_filter.mp hz
    exact ⟨hzG, hfresh, (hF _ hfamily).2.2.1, (hF _ hfamily).2.2.2.1⟩
  have hcover : F ⊆ P.biUnion (fun p ↦ (S p).image fun z ↦ insert z {p.1, p.2}) := by
    intro I hI
    obtain ⟨hIG, hcard, _hconn, _hrank, x, hx, y, hy, hxy, hno, hdim⟩ := hF I hI
    have heI : ({x, y} : Finset ℕ) ⊆ I := by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hx
      · exact mem_singleton.mp hu ▸ hy
    obtain ⟨z, hzI, hfresh, he⟩ := TwoEdgeTripleCover.third_vertex hcard (card_pair hxy) heI
    have hfamily : insert z {x, y} = I := by simpa only [union_singleton] using he.symm
    have hp : (x, y) ∈ P := mem_filter.mpr ⟨mem_product.mpr ⟨hIG hx, hIG hy⟩, hxy, hno, hdim⟩
    have hz : z ∈ S (x, y) := mem_filter.mpr ⟨hIG hzI, hfresh, hfamily.symm ▸ hI⟩
    exact mem_biUnion.mpr ⟨(x, y), hp, mem_image.mpr ⟨z, hz, hfamily⟩⟩
  calc
    _ ≤ ∑ I ∈ P.biUnion (fun p ↦ (S p).image fun z ↦ insert z {p.1, p.2}), infiniteJointMoment L I :=
      sum_le_sum_of_subset_of_nonneg hcover (fun I _ _ ↦ infiniteJointMoment_nonneg L I)
    _ ≤ ∑ p ∈ P, ∑ I ∈ (S p).image (fun z ↦ insert z {p.1, p.2}), infiniteJointMoment L I :=
      GraphStarWeights.sum_biUnion_le_nonneg P _ _ (infiniteJointMoment_nonneg L)
    _ ≤ ∑ p ∈ P, ∑ z ∈ S p, infiniteJointMoment L (insert z {p.1, p.2}) :=
      sum_le_sum fun _p _hp ↦ sum_image_le_of_nonneg (fun I _hI ↦ infiniteJointMoment_nonneg L I)
    _ ≤ _ := h N hN L hband P hP S hS

end PaperP1.StrongNonalignedTripleProfile
