module

public import PaperP1.Model.WeakPairActivity
public import PaperP1.Model.AllAlignedPairs

/-! # The actual weak, nonaligned and boundary dependent-pair seeds for a coarse triple reduction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseTriplePairSeeds

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (N L : ℕ) (θ : ℝ) : Finset (Finset ℕ) :=
  (DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2).filter fun e ↦
    e ∈ WeakPairActivity.pairs (dyadicBlock N) L θ ∨ e ∈ AllAlignedPairs.nonaligned N L ∨
      e ∈ BoundaryAlignedPairs.channel N L 1 1 ∨ e ∈ BoundaryAlignedPairs.channel N L 1 2

theorem mem_pairs (N L : ℕ) (θ : ℝ) (e : Finset ℕ) :
    e ∈ pairs N L θ ↔ e ∈ DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2 ∧
      (e ∈ WeakPairActivity.pairs (dyadicBlock N) L θ ∨ e ∈ AllAlignedPairs.nonaligned N L ∨
        e ∈ BoundaryAlignedPairs.channel N L 1 1 ∨ e ∈ BoundaryAlignedPairs.channel N L 1 2) := by
  exact mem_filter

theorem activity_bound (N L : ℕ) (θ : ℝ) :
    CompatibleActivitySplit.absolute L (pairs N L θ) ≤
      CompatibleActivitySplit.absolute L (WeakPairActivity.pairs (dyadicBlock N) L θ) +
      CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
      CompatibleActivitySplit.absolute L (BoundaryAlignedPairs.channel N L 1 1) +
      CompatibleActivitySplit.absolute L (BoundaryAlignedPairs.channel N L 1 2) := by
  let W := WeakPairActivity.pairs (dyadicBlock N) L θ
  let A := AllAlignedPairs.nonaligned N L
  let B := BoundaryAlignedPairs.channel N L 1 1
  let D := BoundaryAlignedPairs.channel N L 1 2
  let w := fun e : Finset ℕ ↦ |infiniteCenteredCoefficient L e|
  have hsub : pairs N L θ ⊆ ((W ∪ A) ∪ B) ∪ D := by
    intro e he
    have h := ((mem_pairs N L θ e).mp he).2
    simpa only [mem_union, or_assoc] using h
  have hf (e : Finset ℕ) : 0 ≤ w e := abs_nonneg _
  have h0 := sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ hf e)
  have h1 := GraphStarWeights.sum_union_le_nonneg W A w hf
  have h2 := GraphStarWeights.sum_union_le_nonneg (W ∪ A) B w hf
  have h3 := GraphStarWeights.sum_union_le_nonneg ((W ∪ A) ∪ B) D w hf
  change (∑ e ∈ pairs N L θ, w e) ≤ (∑ e ∈ W, w e) + (∑ e ∈ A, w e) +
    (∑ e ∈ B, w e) + ∑ e ∈ D, w e
  linarith only [h0, h1, h2, h3]

end PaperP1.CoarseTriplePairSeeds
