module

public import PaperP1.Model.RetainedActiveSubsetMoments

/-! # The actual compressed-subfamily count is exactly the source's active-pair times admissible-complement count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedPairCountSource

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RetainedActiveSubsetMoments PaperP1.RetainedCardinalityDeficits PaperP1.RegularStarts

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem formula (H : ℝ) (N L r : ℕ) (hr : 2 ≤ r) (A : Finset ℕ) (hAG : A ⊆ regularStarts N L) :
    pair H N L r A = ∑ e ∈ GoodEdgeCompression.goodEdges H N L,
      if e ⊆ A then ((gamma N L e (r - 2)).filter (fun U ↦ U ⊆ A \ e)).card else 0 := by
  apply sum_congr rfl
  intro e he
  by_cases heA : e ⊆ A
  · rw [ite_eq_left heA]
    have h := RetainedSubsetCounts.compressed_layer_reindex (fun x ↦ squareClassSpace x L) A e heA
      (RetainedGoodEdges.good_pair_card H N L e he) r hr (fun _I ↦ (1 : ℕ))
    simp only [sum_const, smul_eq_mul, mul_one] at h
    have hfamilies : ((A \ e).powersetCard (r - 2)).filter
        (fun U ↦ RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ U)) =
        (gamma N L e (r - 2)).filter (fun U ↦ U ⊆ A \ e) := by
      ext U
      simp only [gamma, mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, hcard⟩, hcomp⟩
        exact ⟨⟨⟨hsub.trans (sdiff_subset_sdiff_left e hAG), hcard⟩, hcomp⟩, hsub⟩
      · rintro ⟨⟨⟨_hsub, hcard⟩, hcomp⟩, hsubA⟩
        exact ⟨⟨hsubA, hcard⟩, hcomp⟩
    exact h.trans (congrArg Finset.card hfamilies)
  · rw [ite_eq_right heA, RetainedSubsetCounts.compressedCount_zero_of_not_subset _ A e r heA]

end PaperP1.RetainedPairCountSource
