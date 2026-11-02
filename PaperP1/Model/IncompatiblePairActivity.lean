module

public import PaperP1.Model.WeakPairActivity

/-! # Exact negative pair activity and an unconditional dependent-product majorant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncompatiblePairActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DependentFamilySeeds

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 2) ≤
      ∑ I ∈ dependentFamilies G L 2, ∏ x ∈ I, infiniteMarginal x L := by
  classical
  let F := (dependentFamilies G L 2).filter (fun I ↦ infiniteJointMoment L I = 0)
  have hsub : F ⊆ (G.powersetCard 2).filter (fun I ↦ infiniteJointMoment L I = 0) := by
    intro I hI
    obtain ⟨hdep, hq⟩ := mem_filter.mp hI
    exact mem_filter.mpr ⟨(mem_filter.mp hdep).1, hq⟩
  have heq : CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 2) =
      ∑ I ∈ F, |infiniteCenteredCoefficient L I| := by
    symm
    apply sum_subset hsub
    intro I hI hnot
    obtain ⟨hIG, hq⟩ := mem_filter.mp hI
    have hz : runRelativeNullity L I = 0 := by
      by_contra hn
      exact hnot (mem_filter.mpr ⟨mem_filter.mpr ⟨hIG, Nat.pos_of_ne_zero hn⟩, hq⟩)
    have hp0 : (∏ x ∈ I, infiniteMarginal x L) = 0 := by
      have h := HeterogeneousDirectMaximum.direct_joint_factor L hL I hz
      rw [hq] at h
      exact h.symm
    rw [CompressedJointMoments.centered_pair L I (mem_powersetCard.mp hIG).2, hq, hp0, sub_self, abs_zero]
  calc
    _ = ∑ I ∈ F, |infiniteCenteredCoefficient L I| := heq
    _ = ∑ I ∈ F, ∏ x ∈ I, infiniteMarginal x L := by
      apply sum_congr rfl
      intro I hI
      obtain ⟨hdep, hq⟩ := mem_filter.mp hI
      rw [CompressedJointMoments.centered_pair L I (mem_powersetCard.mp (mem_filter.mp hdep).1).2,
        hq, zero_sub, abs_neg, abs_of_nonneg
          (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun I _ _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)

theorem signed_absolute_gap (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    CompatibleActivitySplit.absolute L (G.powersetCard 2) -
      CompatibleActivitySplit.signed L (G.powersetCard 2) =
        2 * CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 2) := by
  classical
  have hs : CompatibleActivitySplit.incompatibleSigned L (G.powersetCard 2) =
      -CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 2) := by
    unfold CompatibleActivitySplit.incompatibleSigned CompatibleActivitySplit.incompatibleAbsolute
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro I hI
    obtain ⟨hIG, hq⟩ := mem_filter.mp hI
    have hnonpos : infiniteCenteredCoefficient L I ≤ 0 := by
      rw [CompressedJointMoments.centered_pair L I (mem_powersetCard.mp hIG).2, hq, zero_sub]
      exact neg_nonpos.mpr (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    rw [abs_of_nonpos hnonpos, neg_neg]
  rw [CompatibleActivitySplit.absolute_split L hL, CompatibleActivitySplit.signed_split, hs]
  ring

end PaperP1.IncompatiblePairActivity
