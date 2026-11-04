module

public import PaperP1.Model.CompressedPairMass
public import PaperP1.Model.HomogeneousEffectiveWeights
public import PaperP1.Model.EffectiveChannelCompressedPrimitiveSets
public import PaperP1.Model.CompressedSingletonTarget
public import PaperP1.Asymptotics.HomogeneousEffectiveGoodPairExtensionsUnderInputs

/-! # Literal original compressed activity above each actual raw good channel

All target windows are allowed, including irregular and incompatible ones.
The source pair remains distinguished in every sum.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelCompressedActivityBounds

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def pairs (N H a b L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (CompressedPairMass.pairs (dyadicBlock N) L).filter fun p ↦ p.1 ∈ PrivateChannelActivity.pairs N H a b L

def separated (N H a b L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (pairs N H a b L).filter fun p ↦ SeparatedHomogeneousMass.Separated L (p.1 ∪ p.2)

def high (N H a b L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (pairs N H a b L).filter fun p ↦ 2 ≤ p.2.card

def single (N H a b L : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (separated N H a b L).filter fun p ↦ p.2.card = 1

def homogeneousWeight (L : ℕ) (w : ℝ) (p : Finset ℕ × Finset ℕ) : ℝ :=
  w ^ (p.2.card + 2) * HomogeneousRunMass.probability L (p.1 ∪ p.2)

def singletonLift (p : Finset ℕ × ℕ) : Finset ℕ × Finset ℕ := (p.1, {p.2})

theorem data {N H a b L : ℕ} {p : Finset ℕ × Finset ℕ} (hp : p ∈ pairs N H a b L) :
    p.1.card = 2 ∧ p.2 ⊆ dyadicBlock N ∧ PairPrimitiveCompression.Primitive L p.1 p.2 ∧
      p.1 ∈ PrivateChannelActivity.pairs N H a b L := by
  obtain ⟨hpP, hpE⟩ := mem_filter.mp hp
  have hd := CompressedPairMass.mem_pairs _ _ _ |>.mp hpP
  exact ⟨hd.2.1, hd.2.2.1, hd.2.2.2.2, hpE⟩

theorem homogeneousWeight_nonneg (L : ℕ) (w : ℝ) (hw : 0 ≤ w) (p : Finset ℕ × Finset ℕ) :
    0 ≤ homogeneousWeight L w p :=
  mul_nonneg (pow_nonneg hw _) (HomogeneousRunMass.probability_pos L _).le

theorem mass_le_homogeneous {N H a b L : ℕ} (hL : 0 < L) (w : ℝ) (hw : 0 ≤ w)
    (P : Finset (Finset ℕ × Finset ℕ)) (hP : P ⊆ pairs N H a b L) :
    CompressedPairMass.mass P L w ≤ 4 * ∑ p ∈ P, homogeneousWeight L w p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  have hd := data (hP hp)
  exact (mul_le_mul_of_nonneg_left
    (HomogeneousEffectiveWeights.compressed_three_mass_le L hL p.1 p.2 hd.1 hd.2.2.1)
    (pow_nonneg hw _)).trans_eq (by unfold homogeneousWeight; ring)

theorem high_homogeneous_bound (N H a b L : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ p ∈ high N H a b L, homogeneousWeight L w p) ≤
      EffectiveChannelCompressedPrimitiveSets.mass N a b L 2 w := by
  let f := fun q : (ℕ × ℕ) × Finset ℕ ↦ (({q.1.1, q.1.2} : Finset ℕ), q.2)
  let Q := EffectiveChannelCompressedPrimitiveSets.points N a b L 2
  have hsub : high N H a b L ⊆ Q.image f := by
    intro p hp
    obtain ⟨hpP, hsize⟩ := mem_filter.mp hp
    obtain ⟨_he, hAG, hprim, heRaw⟩ := data hpP
    obtain ⟨xy, hxy, hpair⟩ := mem_image.mp heRaw
    apply mem_image.mpr
    refine ⟨(xy, p.2), ?_, Prod.ext hpair rfl⟩
    apply EffectiveChannelCompressedPrimitiveSets.mem_points.mpr
    refine ⟨PrivateChannelSources.good_sources_subset_unitSources N H a b L hxy, hAG, hsize, ?_⟩
    rw [hpair]
    exact hprim
  calc
    _ ≤ ∑ p ∈ Q.image f, homogeneousWeight L w p :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ homogeneousWeight_nonneg L w hw p)
    _ ≤ ∑ q ∈ Q, homogeneousWeight L w (f q) :=
      sum_image_le_of_nonneg (fun p _ ↦ homogeneousWeight_nonneg L w hw p)
    _ = _ := by rw [EffectiveChannelCompressedPrimitiveSets.mass_eq_points]; rfl

theorem high_mass_bound {N H a b L : ℕ} (hL : 0 < L) (w : ℝ) (hw : 0 ≤ w) :
    CompressedPairMass.mass (high N H a b L) L w ≤
      4 * EffectiveChannelCompressedPrimitiveSets.mass N a b L 2 w :=
  (mass_le_homogeneous hL w hw _ (filter_subset _ _)).trans
    (mul_le_mul_of_nonneg_left (high_homogeneous_bound N H a b L w hw) (by norm_num))

theorem single_subset (N H a b L : ℕ) : single N H a b L ⊆
    (HomogeneousEffectiveGoodPairExtensionsUnderInputs.points N H a b L).image singletonLift := by
  intro p hp
  obtain ⟨hpS, hcard⟩ := mem_filter.mp hp
  obtain ⟨hpP, hsep⟩ := mem_filter.mp hpS
  obtain ⟨_he, hAG, hprim, heRaw⟩ := data hpP
  obtain ⟨z, hz⟩ := card_eq_one.mp hcard
  have hzN : z ∈ dyadicBlock N := hAG (hz.symm ▸ mem_singleton_self z)
  have hprim' : PairPrimitiveCompression.Primitive L p.1 {z} := hz ▸ hprim
  refine mem_image.mpr ⟨(p.1, z), ?_, ?_⟩
  · apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨heRaw, hzN⟩, disjoint_singleton_right.mp hprim'.1, ?_,
      CompressedSingletonTarget.rank_pos L p.1 z hprim'⟩
    change SeparatedHomogeneousMass.Separated L (p.1 ∪ {z})
    rw [← hz]
    exact hsep
  · exact Prod.ext rfl hz.symm

theorem single_homogeneous_bound (N H a b L : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ p ∈ single N H a b L, homogeneousWeight L w p) ≤
      w ^ 3 * HomogeneousEffectiveGoodPairExtensionsUnderInputs.mass N H a b L := by
  calc
    _ ≤ ∑ p ∈ (HomogeneousEffectiveGoodPairExtensionsUnderInputs.points N H a b L).image singletonLift,
        homogeneousWeight L w p := sum_le_sum_of_subset_of_nonneg (single_subset N H a b L)
          (fun p _ _ ↦ homogeneousWeight_nonneg L w hw p)
    _ ≤ ∑ q ∈ HomogeneousEffectiveGoodPairExtensionsUnderInputs.points N H a b L,
        homogeneousWeight L w (singletonLift q) :=
      sum_image_le_of_nonneg (fun p _ ↦ homogeneousWeight_nonneg L w hw p)
    _ = _ := by
      rw [HomogeneousEffectiveGoodPairExtensionsUnderInputs.mass, mul_sum]
      apply sum_congr rfl
      intro q _
      simp only [homogeneousWeight, singletonLift, card_singleton, show 1 + 2 = 3 by decide]
      rfl

theorem single_mass_bound {N H a b L : ℕ} (hL : 0 < L) (w : ℝ) (hw : 0 ≤ w) :
    CompressedPairMass.mass (single N H a b L) L w ≤
      4 * w ^ 3 * HomogeneousEffectiveGoodPairExtensionsUnderInputs.mass N H a b L := by
  have hsub : single N H a b L ⊆ pairs N H a b L :=
    (filter_subset _ _).trans (filter_subset _ _)
  exact (mass_le_homogeneous hL w hw _ hsub).trans
    ((mul_le_mul_of_nonneg_left (single_homogeneous_bound N H a b L w hw) (by norm_num)).trans_eq (by ring))

theorem separated_mass_bound (N H a b L : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    CompressedPairMass.mass (separated N H a b L) L w ≤
      CompressedPairMass.mass (high N H a b L) L w + CompressedPairMass.mass (single N H a b L) L w := by
  have hcover : separated N H a b L ⊆ high N H a b L ∪ single N H a b L := by
    intro p hp
    have hd := data (mem_filter.mp hp).1
    have hpos := (PairPrimitiveCompression.nonempty L p.1 p.2 hd.2.2.1).card_pos
    by_cases hhigh : 2 ≤ p.2.card
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp hp).1, hhigh⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, by omega⟩)
  apply (CompressedPairMass.mass_mono _ _ hcover L w hw).trans
  apply GraphStarWeights.sum_union_le_nonneg
  intro p
  exact mul_nonneg (pow_nonneg hw _)
    (add_nonneg (add_nonneg (infiniteJointMoment_nonneg L _) (abs_nonneg _)) (abs_nonneg _))

end PaperP1.ChannelCompressedActivityBounds
