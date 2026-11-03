module

public import PaperP1.Model.DirectPairProductComparison
public import PaperP1.Model.DirectRunBlocks
public import PaperP1.Model.FiniteGoodChannelPartition
public import PaperP1.Arithmetic.CompressedPairIntersectionHosts

/-! # Literal disjoint non-direct products in the retained finite channel classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodApartPairProducts

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteAlignedChannelCover PaperP1.PrivateChannelSources

def families (Q N H L : ℕ) : Finset (Finset (Finset ℕ)) := by
  classical
  exact (DirectPairProductComparison.nonDirectApartPairs (dyadicBlock N) L).filter
    (fun S ↦ S ⊆ FiniteGoodChannelPartition.good Q N H L)

def mass (Q N H L : ℕ) : ℝ :=
  ∑ S ∈ families Q N H L, ∏ e ∈ S, |infiniteCenteredCoefficient L e|

theorem span_pair (L x y : ℕ) :
    SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {x, y} =
      squareClassSpace x L ⊔ squareClassSpace y L := by
  rw [SubspaceFamilyRank.span_insert]
  have hs : SubspaceFamilyRank.span (fun z ↦ squareClassSpace z L) {y} = squareClassSpace y L := by
    simp [SubspaceFamilyRank.span]
  rw [hs]

theorem nonDirect_intersection {G : Finset ℕ} {L : ℕ} {e f : Finset ℕ}
    (hef : e ≠ f) (hS : {e, f} ∈ DirectPairProductComparison.nonDirectApartPairs G L) :
    SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e ⊓
      SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) f ≠ ⊥ := by
  classical
  obtain ⟨hSE, hnot, hnd⟩ := mem_filter.mp hS
  have he := (mem_powersetCard.mp hSE).1 (show e ∈ ({e, f} : Finset (Finset ℕ)) by simp)
  have hf := (mem_powersetCard.mp hSE).1 (show f ∈ ({e, f} : Finset (Finset ℕ)) by simp)
  have hdis : Disjoint e f := by
    by_contra hd
    exact hnot ((SharedPairProducts.pair_mem_overlapping G e f he hf hef).mpr hd)
  intro hz
  exact hnd ((DirectPairProductComparison.direct_pair_iff L e f hef).mpr
    ((DirectRunBlocks.additive_iff_spaces L e f hdis).mpr (disjoint_iff.mpr hz)))

theorem finite_cover (Q N H L : ℕ) :
    families Q N H L ⊆ ((channels Q) ×ˢ (channels Q)).biUnion
      (fun abcd ↦ (CompressedPairIntersectionHosts.allPairs N
        abcd.1.1 abcd.1.2 abcd.2.1 abcd.2.2 L).image
          (fun p ↦ ({({p.1.1, p.1.2} : Finset ℕ), {p.2.1, p.2.2}}))) := by
  classical
  intro S hS
  obtain ⟨hS, hgood⟩ := mem_filter.mp hS
  obtain ⟨e, f, hef, hpair⟩ := card_eq_two.mp (mem_powersetCard.mp (mem_filter.mp hS).1).2
  subst S
  have hdep := nonDirect_intersection hef hS
  obtain ⟨_he, _hqe, ab, hab, heab⟩ := FiniteGoodChannelPartition.good_data (hgood (show e ∈ ({e, f} : Finset (Finset ℕ)) by simp))
  obtain ⟨_hf, _hqf, cd, hcd, hfcd⟩ := FiniteGoodChannelPartition.good_data (hgood (show f ∈ ({e, f} : Finset (Finset ℕ)) by simp))
  obtain ⟨xy, hxy, hexy⟩ := mem_image.mp heab
  obtain ⟨zw, hzw, hfzw⟩ := mem_image.mp hfcd
  obtain ⟨hx, hy, hu, _hp⟩ := mem_goodSources.mp hxy
  obtain ⟨hz, hw, hv, _hq⟩ := mem_goodSources.mp hzw
  rw [← hexy, ← hfzw] at hdep ⊢
  rw [span_pair, span_pair] at hdep
  exact mem_biUnion.mpr ⟨(ab, cd), mem_product.mpr ⟨hab, hcd⟩,
    mem_image.mpr ⟨(xy, zw), mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_product.mpr ⟨hx, hy⟩, mem_product.mpr ⟨hz, hw⟩⟩,
        card_pos.mp (show 0 < (NormalizedUnitCount.units ab.1 ab.2 xy.1 xy.2 L).card by omega),
        card_pos.mp (show 0 < (NormalizedUnitCount.units cd.1 cd.2 zw.1 zw.2 L).card by omega), hdep⟩, rfl⟩⟩

theorem finite_count (Q N H L : ℕ) :
    (families Q N H L).card ≤ ∑ abcd ∈ (channels Q) ×ˢ (channels Q),
      (CompressedPairIntersectionHosts.allPairs N abcd.1.1 abcd.1.2 abcd.2.1 abcd.2.2 L).card := by
  classical
  exact ((card_le_card (finite_cover Q N H L)).trans card_biUnion_le).trans
    (sum_le_sum fun _ _ ↦ card_image_le)

end PaperP1.GoodApartPairProducts
