module

public import PaperP1.Model.AllAlignedPairs
public import PaperP1.Asymptotics.NormalizedDefectPairActivity

/-! # All actual aligned coefficients have a finite principal/boundary/defect/tail cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalAlignedCover

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedUnitCount PaperP1.PrivateChannelSources PaperP1.PrivateUnitCovariance

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem one_unit_zero {N H L a b x y : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hxy : x < y) (hL : 0 < L)
    (hprivate : GoodEdgeCompression.PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L))
    (hu : (units a b x y L).card ≤ 1) : infiniteCenteredCoefficient L {x, y} = 0 := by
  have hx2 := hN.trans (mem_Ico.mp hx).1
  have hy2 := hN.trans (mem_Ico.mp hy).1
  obtain ⟨hpx, hpy⟩ := private_marginals ha (ha.trans hab) hx2 hy2 hL hprivate.private
  have hc := private_pair_covariance ha (ha.trans hab) hx2 hy2 hxy.ne hL hprivate.private
  rw [UnitFourierWeight.signed_unit_sum_zero_of_card_le_one hu, mul_zero] at hc
  rw [CompressedJointMoments.centered_pair L {x, y} (card_pair_eq_two_iff.mpr hxy.ne),
    prod_pair hxy.ne, hpx, hpy, ← pow_two]
  exact hc

theorem channel_nonzero_cover {N H L a b : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hheight : b ≤ (L + 1) ^ 3) (hL : 0 < L)
    {e : Finset ℕ} (he : e ∈ BoundaryAlignedPairs.channel N L a b) (hn : infiniteCenteredCoefficient L e ≠ 0) :
    e ∈ PrivateChannelActivity.pairs N H a b L ∪ NormalizedDefectPairActivity.pairs N H a b L ∪
      AlignedChannelFamilies.zeroFamilies N L := by
  have heN := (mem_filter.mp he).1
  obtain ⟨x, y, hx, hy, rfl, hxy, hg⟩ := BoundaryAlignedPairs.data he
  by_cases hu : (units a b x y L).Nonempty
  · by_cases hprivate : GoodEdgeCompression.PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L)
    · by_cases htwo : 2 ≤ (units a b x y L).card
      · apply mem_union_left
        apply mem_union_left
        exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, htwo, hprivate⟩, rfl⟩
      · exact False.elim (hn (one_unit_zero hN ha hab hx hy hxy hL hprivate (by omega)))
    · apply mem_union_left
      apply mem_union_right
      exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hu, hprivate⟩, rfl⟩
  · apply mem_union_right
    exact mem_filter.mpr ⟨heN, x, y, a, b, rfl, hxy, ha, ha.trans hab, hcop,
      by simpa only [max_eq_right hab.le] using hheight, hg,
      Nat.eq_zero_of_not_pos (fun hp ↦ hu (card_pos.mp hp))⟩

def classes (N H L : ℕ) (i : ℕ) : Finset (Finset ℕ) :=
  if i = 0 then BoundaryAlignedPairs.channel N L 1 1 else
  if i = 1 then BoundaryAlignedPairs.channel N L 1 2 else
  if i = 2 then PrivateChannelActivity.pairs N H 2 3 L else
  if i = 3 then PrivateChannelActivity.pairs N H 3 4 L else
  if i = 4 then NormalizedDefectPairActivity.pairs N H 2 3 L else
  if i = 5 then NormalizedDefectPairActivity.pairs N H 3 4 L else
  if i = 6 then AlignedChannelFamilies.zeroFamilies N L else
    AlignedChannelFamilies.families N L 5

theorem finite_bound {N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hheight : 4 ≤ (L + 1) ^ 3)
    (hlarge : 2 * (L + 1) ^ 4 < N) :
    CompatibleActivitySplit.absolute L (AllAlignedPairs.families N L) ≤
      CompatibleActivitySplit.absolute L (BoundaryAlignedPairs.channel N L 1 1) +
      CompatibleActivitySplit.absolute L (BoundaryAlignedPairs.channel N L 1 2) +
      CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N H 2 3 L) +
      CompatibleActivitySplit.absolute L (PrivateChannelActivity.pairs N H 3 4 L) +
      CompatibleActivitySplit.absolute L (NormalizedDefectPairActivity.pairs N H 2 3 L) +
      CompatibleActivitySplit.absolute L (NormalizedDefectPairActivity.pairs N H 3 4 L) +
      CompatibleActivitySplit.absolute L (AlignedChannelFamilies.zeroFamilies N L) +
      CompatibleActivitySplit.absolute L (AlignedChannelFamilies.families N L 5) := by
  have hcover : ∀ e ∈ AllAlignedPairs.families N L, infiniteCenteredCoefficient L e ≠ 0 →
      ∃ i ∈ range 8, e ∈ classes N H L i := by
    intro e he hn
    rcases AllAlignedPairs.classification hlarge he with h1 | h2 | h23 | h34 | htail
    · exact ⟨0, by decide, by simpa only [classes, ite_true] using h1⟩
    · exact ⟨1, by decide, by simpa only [classes, show ¬(1 : ℕ) = 0 by decide, ite_false, ite_true] using h2⟩
    · have hc := channel_nonzero_cover (H := H) hN (by decide : 0 < 2) (by decide : 2 < 3)
        (by decide) (by omega) hL h23 hn
      rcases mem_union.mp hc with h | hz
      · rcases mem_union.mp h with hg | hb
        · exact ⟨2, by decide, by simpa [classes] using hg⟩
        · exact ⟨4, by decide, by simpa [classes] using hb⟩
      · exact ⟨6, by decide, by simpa [classes] using hz⟩
    · have hc := channel_nonzero_cover (H := H) hN (by decide : 0 < 3) (by decide : 3 < 4)
        (by decide) hheight hL h34 hn
      rcases mem_union.mp hc with h | hz
      · rcases mem_union.mp h with hg | hb
        · exact ⟨3, by decide, by simpa [classes] using hg⟩
        · exact ⟨5, by decide, by simpa [classes] using hb⟩
      · exact ⟨6, by decide, by simpa [classes] using hz⟩
    · exact ⟨7, by decide, by simpa [classes] using htail⟩
  have h := ActivityFamilyCover.finite_cover L (AllAlignedPairs.families N L) (range 8) (classes N H L) hcover
  simpa only [sum_range_succ, sum_range_zero, classes, ite_true, ite_false, Nat.reduceEqDiff,
    Nat.reduceEqDiff, zero_add] using h

end PaperP1.PrincipalAlignedCover
