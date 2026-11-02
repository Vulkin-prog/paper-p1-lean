module

public import PaperP1.Model.LogHeightUnitChannelFamily
public import PaperP1.Model.PairLossWeights
public import PaperP1.Model.WeakPairActivity
public import PaperP1.Model.AbsoluteActivityDecomposition
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Literal enlarged aligned families split into exact-unit and zero-unit populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedChannelFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.EnlargedPairGeometry

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def ZeroUnitAlignment (L : ℕ) (e : Finset ℕ) : Prop :=
  ∃ x y a b : ℕ, e = {x, y} ∧ x < y ∧ 0 < a ∧ 0 < b ∧ a.Coprime b ∧
    max a b ≤ (L + 1) ^ 3 ∧ Geometric a b x y L ∧ (units a b x y L).card = 0

def zeroFamilies (N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 2).filter (ZeroUnitAlignment L)

def families (N L b₀ : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 2).filter fun e ↦
    ∃ ab ∈ LogHeightUnitChannelFamily.channels L b₀, ∃ x y : ℕ,
      e = {x, y} ∧ x < y ∧ Geometric ab.1 ab.2 x y L

theorem relative_le_loss {x y L : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    runRelativeNullity L {x, y} ≤ pairLoss x y L := by
  rw [runRelativeNullity, RetainedNullity.nullity_pair_eq_intersection _ _ _ hxy]
  exact intersection_rank_le_loss hx hy

theorem cover (N L b₀ : ℕ) :
    families N L b₀ ⊆ LogHeightUnitChannelFamily.families N L b₀ ∪ zeroFamilies N L := by
  intro e he
  obtain ⟨hecard, ab, hab, x, y, rfl, hxy, hgeom⟩ := mem_filter.mp he
  obtain ⟨ha, hablt, hcop, _hbb, hheight⟩ := LogHeightUnitChannelFamily.channel_data hab
  obtain ⟨heN, _⟩ := mem_powersetCard.mp hecard
  have hx := heN (mem_insert_self x {y})
  have hy := heN (mem_insert_of_mem (mem_singleton_self y))
  by_cases hu : (units ab.1 ab.2 x y L).Nonempty
  · apply mem_union_left
    exact mem_biUnion.mpr ⟨ab, hab, mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hu⟩, rfl⟩⟩
  · apply mem_union_right
    apply mem_filter.mpr
    refine ⟨hecard, x, y, ab.1, ab.2, rfl, hxy, ha, ha.trans hablt, hcop, ?_, hgeom, ?_⟩
    · rw [max_eq_right hablt.le]
      exact hheight
    · exact Nat.eq_zero_of_not_pos (fun h ↦ hu (card_pos.mp h))

theorem activity_bound (N L b₀ : ℕ) :
    CompatibleActivitySplit.absolute L (families N L b₀) ≤
      CompatibleActivitySplit.absolute L (LogHeightUnitChannelFamily.families N L b₀) +
        CompatibleActivitySplit.absolute L (zeroFamilies N L) := by
  let U := LogHeightUnitChannelFamily.families N L b₀
  let Z := zeroFamilies N L
  calc
    _ ≤ ∑ e ∈ U ∪ Z, |infiniteCenteredCoefficient L e| :=
      sum_le_sum_of_subset_of_nonneg (cover N L b₀) (fun _ _ _ ↦ abs_nonneg _)
    _ ≤ _ := by
      have heq := sum_union_inter (s₁ := U) (s₂ := Z) (f := fun e ↦ |infiniteCenteredCoefficient L e|)
      have hi : 0 ≤ ∑ e ∈ U ∩ Z, |infiniteCenteredCoefficient L e| := sum_nonneg fun _ _ ↦ abs_nonneg _
      change _ ≤ (∑ e ∈ U, |infiniteCenteredCoefficient L e|) + ∑ e ∈ Z, |infiniteCenteredCoefficient L e|
      linarith only [heq, hi]

end PaperP1.AlignedChannelFamilies
