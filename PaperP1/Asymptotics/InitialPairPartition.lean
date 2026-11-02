module

public import PaperP1.Asymptotics.WeakPairActivity
public import PaperP1.Asymptotics.IrregularPairActivity
public import PaperP1.Model.AbsoluteActivityDecomposition

/-! # An exact first partition of dependent pairs with two checked source-scale classes

The remaining class consists of compatible regular pairs of macroscopic
nullity. Its further rational-channel and nonaligned analysis is separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InitialPairPartition

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DependentFamilySeeds

def exceptional (G : Finset ℕ) (N L : ℕ) : Finset (Finset ℕ) :=
  dependentFamilies G L 2 ∩ IrregularPairActivity.pairs N L G

def weak (G : Finset ℕ) (N L : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  WeakPairActivity.pairs G L η \ exceptional G N L

def remaining (G : Finset ℕ) (N L : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  dependentFamilies G L 2 \ (weak G N L η ∪ exceptional G N L)

theorem weak_disjoint_exceptional (G : Finset ℕ) (N L : ℕ) (η : ℝ) :
    Disjoint (weak G N L η) (exceptional G N L) := by
  apply disjoint_left.mpr
  intro I hw he
  exact (mem_sdiff.mp hw).2 he

theorem cover (G : Finset ℕ) (N L : ℕ) (η : ℝ) :
    (weak G N L η ∪ exceptional G N L) ∪ remaining G N L η = dependentFamilies G L 2 := by
  classical
  ext I
  constructor
  · intro hI
    rcases mem_union.mp hI with hwe | hr
    · rcases mem_union.mp hwe with hw | he
      · exact (mem_filter.mp (mem_sdiff.mp hw).1).1
      · exact (mem_inter.mp he).1
    · exact (mem_sdiff.mp hr).1
  · intro hI
    by_cases hwe : I ∈ weak G N L η ∪ exceptional G N L
    · exact mem_union_left _ hwe
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hI, hwe⟩)

theorem remaining_data (G : Finset ℕ) (N L : ℕ) (η : ℝ) (I : Finset ℕ)
    (hI : I ∈ remaining G N L η) :
    I ∈ dependentFamilies G L 2 ∧ I ∉ IrregularPairActivity.pairs N L G ∧
      η * L < (runRelativeNullity L I : ℝ) ∧ 0 < infiniteJointMoment L I := by
  classical
  obtain ⟨hdep, hnot⟩ := mem_sdiff.mp hI
  have he : I ∉ exceptional G N L := fun h ↦ hnot (mem_union_right _ h)
  have hw : ¬WeakPairActivity.Weak L η I := by
    intro h
    exact hnot (mem_union_left _ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨hdep, h⟩, he⟩))
  have hlow : ¬(runRelativeNullity L I : ℝ) ≤ η * L := fun h ↦ hw (Or.inl h)
  have hq : infiniteJointMoment L I ≠ 0 := fun h ↦ hw (Or.inr h)
  exact ⟨hdep, fun h ↦ he (mem_inter.mpr ⟨hdep, h⟩), lt_of_not_ge hlow,
    lt_of_le_of_ne (infiniteJointMoment_nonneg L I) (Ne.symm hq)⟩

theorem activity_split (G : Finset ℕ) (N L : ℕ) (hL : 0 < L) (η : ℝ) :
    CompatibleActivitySplit.absolute L (G.powersetCard 2) =
      CompatibleActivitySplit.absolute L (weak G N L η) +
        CompatibleActivitySplit.absolute L (exceptional G N L) +
          CompatibleActivitySplit.absolute L (remaining G N L η) := by
  have hdis : Disjoint (weak G N L η ∪ exceptional G N L) (remaining G N L η) := by
    apply disjoint_left.mpr
    intro I hwe hr
    exact (mem_sdiff.mp hr).2 hwe
  calc
    _ = ∑ I ∈ dependentFamilies G L 2, |infiniteCenteredCoefficient L I| :=
      AbsoluteActivityDecomposition.absolute_eq_dependent G L 2 hL (by omega)
    _ = _ := by
      rw [← cover G N L η, sum_union hdis, sum_union (weak_disjoint_exceptional G N L η)]
      rfl

theorem uniform_bounds (C η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (weak G N L η) ≤ (N : ℝ) ^ (-1 + η + ε) ∧
      CompatibleActivitySplit.absolute L (exceptional G N L) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NW, _hNW, hw⟩ := WeakPairActivityAsymptotic.uniform_activity C η ε hη hε
  obtain ⟨NE, _hNE, he⟩ := IrregularPairActivity.uniform_activity C ε hε
  refine ⟨max 2 (max NW NE), by omega, ?_⟩
  intro N hN L hband G hG
  constructor
  · exact (sum_le_sum_of_subset_of_nonneg sdiff_subset
      (fun I _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))).trans (hw N (by omega) L hband G hG)
  · exact (sum_le_sum_of_subset_of_nonneg inter_subset_right
      (fun I _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))).trans (he N (by omega) L hband G hG)

end PaperP1.InitialPairPartition
