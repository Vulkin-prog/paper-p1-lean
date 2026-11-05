module

public import PaperP1.Asymptotics.NonalignedPairActivity
public import PaperP1.Asymptotics.DenseNonalignedProfileReduction

/-! # Unconditional actual activity for the dense nonaligned pair sector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePairActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.DenseNonalignedProfileReduction

theorem nonaligned_host {N L x y : ℕ} (hxy : x ≠ y)
    (he : {x, y} ∈ AllAlignedPairs.nonaligned N L) :
    ¬CompressedTargetAlignment.Aligned 1 x y L := by
  classical
  intro ha
  obtain ⟨heN, hnot⟩ := mem_sdiff.mp he
  apply hnot
  apply mem_filter.mpr
  refine ⟨heN, ?_⟩
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact ⟨x, y, rfl, hlt, ha⟩
  · exact ⟨y, x, pair_comm x y, hgt, DegreeOneGraphHostCount.alignment_symm ha⟩

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (dense N L) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨N₀, hN₀, h⟩ := NonalignedPairActivity.uniform_activity C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  exact (sum_le_sum_of_subset_of_nonneg (inter_subset_left : dense N L ⊆ AllAlignedPairs.nonaligned N L)
    (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans (h N hN L hband)

end PaperP1.DensePairActivity
