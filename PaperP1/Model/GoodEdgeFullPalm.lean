module

public import PaperP1.Model.GoodEdgePositivePalm
public import PaperP1.Asymptotics.FixedChannelAlignedTargetMass

/-! # Full original Palm costs split into marginal bias and actual crossings

The target population may contain every irregular original start. All unit
offsets are kept in a finite cover of the actual unordered source population.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgeFullPalm

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.GoodEdgePositivePalm PaperP1.DyadicEndpointPairs PaperP1.CompressedSourceBlocks
  PaperP1.SubspaceFamilyRank

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def crossingPoints (N H a b L : ℕ) (G : Finset ℕ) : Finset (Finset ℕ × ℕ) :=
  (GoodEdgePositivePalm.points N H a b L G).filter fun p ↦ 0 < OneTargetCrossing.rank p.1 L p.2

def crossingMass (N H a b L : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ p ∈ crossingPoints N H a b L G, infiniteJointMoment L (insert p.2 p.1)

def encode (p : (ℕ × ℕ) × ℕ) : Finset ℕ × ℕ := ({p.1.1, p.1.2}, p.2)

def codes (N a b L : ℕ) (i j : Fin (L + 1)) : Finset ((ℕ × ℕ) × ℕ) :=
  FixedChannelAlignedTargetMass.points N a b L i j ∪ CompressedNonalignedInteractionMass.points N a b L i j

theorem encode_joint (L : ℕ) (p : (ℕ × ℕ) × ℕ) :
    infiniteJointMoment L (insert (encode p).2 (encode p).1) =
      infiniteJointMoment L {p.1.1, p.1.2, p.2} := by
  congr 1
  exact (insert_comm p.2 p.1.1 {p.1.2}).trans (congrArg (insert p.1.1) (pair_comm p.2 p.1.2))

theorem excess_split (L : ℕ) (hL : 0 < L) (e : Finset ℕ) (z : ℕ) (hfresh : z ∉ e) :
    excess L e z ≤ infiniteJointMoment L e * |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹| +
      if 0 < OneTargetCrossing.rank e L z then infiniteJointMoment L (insert z e) else 0 := by
  have hq := infiniteJointMoment_nonneg L e
  have hb : 0 ≤ infiniteJointMoment L e * |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹| := mul_nonneg hq (abs_nonneg _)
  by_cases hr : 0 < OneTargetCrossing.rank e L z
  · rw [ite_eq_left hr]
    apply max_le (add_nonneg hb (infiniteJointMoment_nonneg L _))
    have hp : 0 ≤ (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L e := mul_nonneg (by positivity) hq
    change infiniteJointMoment L (insert z e) - (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L e ≤ _
    linarith only [hp, hb]
  · rw [ite_eq_right hr, add_zero]
    have hzero : OneTargetCrossing.rank e L z = 0 := by omega
    have hu := OneTargetCrossing.joint_upper e L z hL hfresh
    rw [hzero, pow_zero, mul_one] at hu
    have ha := mul_le_mul_of_nonneg_left (le_abs_self (infiniteMarginal z L - (2 ^ L : ℝ)⁻¹)) hq
    apply max_le hb
    change infiniteJointMoment L (insert z e) - (2 ^ L : ℝ)⁻¹ * infiniteJointMoment L e ≤ _
    nlinarith only [hu, ha]

theorem finite_split (N H a b L : ℕ) (hL : 0 < L) (G : Finset ℕ) :
    GoodEdgePositivePalm.mass N H a b L G ≤
      beta N H a b L * (∑ z ∈ G, |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹|) +
        crossingMass N H a b L G := by
  rw [mass_eq_excess_sum]
  have hpoint := sum_le_sum fun p (hp : p ∈ GoodEdgePositivePalm.points N H a b L G) ↦
    excess_split L hL p.1 p.2 (mem_filter.mp hp).2
  have hbase : (∑ p ∈ GoodEdgePositivePalm.points N H a b L G,
      infiniteJointMoment L p.1 * |infiniteMarginal p.2 L - (2 ^ L : ℝ)⁻¹|) ≤
      beta N H a b L * (∑ z ∈ G, |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹|) := by
    calc
      _ ≤ ∑ p ∈ CompatibleChannelEdges.edges N H a b L ×ˢ G,
          infiniteJointMoment L p.1 * |infiniteMarginal p.2 L - (2 ^ L : ℝ)⁻¹| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun p _ _ ↦ mul_nonneg (infiniteJointMoment_nonneg L _) (abs_nonneg _))
      _ = _ := by
        rw [sum_product, beta, sum_mul]
        apply sum_congr rfl
        intro e _
        change (∑ z ∈ G, infiniteJointMoment L e * |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹|) = _
        exact (mul_sum G (fun z ↦ |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹|) (infiniteJointMoment L e)).symm
  rw [sum_add_distrib, ← sum_filter] at hpoint
  exact hpoint.trans (add_le_add hbase le_rfl)

theorem finite_cover {N H a b L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    crossingPoints N H a b L G ⊆
      univ.biUnion fun ij : Fin (L + 1) × Fin (L + 1) ↦ (codes N a b L ij.1 ij.2).image encode := by
  intro p hp
  obtain ⟨hpP, hcross⟩ := mem_filter.mp hp
  obtain ⟨hpB, hfresh⟩ := mem_filter.mp hpP
  obtain ⟨he, hz⟩ := mem_product.mp hpB
  obtain ⟨xy, hxy, hpair⟩ := mem_image.mp (mem_filter.mp he).1
  obtain ⟨hx, hy, hcount, _hprivate⟩ := PrivateChannelSources.mem_goodSources.mp hxy
  obtain ⟨ij, hij⟩ := card_pos.mp (show 0 < (NormalizedUnitCount.units a b xy.1 xy.2 L).card by omega)
  have hsource : xy ∈ sourcePairs N a b L ij.1 ij.2 :=
    mem_sourcePairs.mpr ⟨hx, hy, NormalizedUnitCount.mem_units.mp hij⟩
  have hzx : p.2 ≠ xy.1 := by intro hh; apply hfresh; rw [hh, ← hpair]; simp
  have hzy : p.2 ≠ xy.2 := by intro hh; apply hfresh; rw [hh, ← hpair]; simp
  have hc : 0 < AsymmetricJointWeight.crossRank xy.1 xy.2 p.2 L := by
    rw [← hpair] at hcross
    have hs : OneTargetCrossing.sourceSpace {xy.1, xy.2} L = squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
      rw [OneTargetCrossing.sourceSpace, span_insert]
      simp [span]
    change 0 < Module.finrank F₂ ↥(squareClassSpace p.2 L ⊓ OneTargetCrossing.sourceSpace {xy.1, xy.2} L) at hcross
    rw [hs, inf_comm] at hcross
    exact hcross
  apply mem_biUnion.mpr
  refine ⟨ij, mem_univ _, mem_image.mpr ⟨(xy, p.2), ?_, Prod.ext hpair rfl⟩⟩
  by_cases halign : CompressedTargetAlignment.Aligned b (anchor b L ij.1 xy) p.2 L
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨hsource, hG hz⟩, hzx, hzy, halign⟩)
  · exact mem_union_right _ (mem_filter.mpr
      ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hsource, hG hz⟩, halign⟩, hzx, hzy, hc⟩)

theorem crossing_bound {N H a b L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    crossingMass N H a b L G ≤ FixedChannelAlignedTargetMass.channelMass N a b L +
      CompressedNonalignedInteractionMass.channelMass N a b L := by
  have h0 := sum_le_sum_of_subset_of_nonneg (finite_cover (H := H) (a := a) (b := b) (L := L) hG)
    (fun p _ _ ↦ infiniteJointMoment_nonneg L (insert p.2 p.1))
  have h1 := GraphStarWeights.sum_biUnion_le_nonneg (univ : Finset (Fin (L + 1) × Fin (L + 1)))
    (fun ij ↦ (codes N a b L ij.1 ij.2).image encode)
    (fun p ↦ infiniteJointMoment L (insert p.2 p.1))
    (fun p ↦ infiniteJointMoment_nonneg L _)
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1),
        ∑ p ∈ (codes N a b L ij.1 ij.2).image encode, infiniteJointMoment L (insert p.2 p.1) := h0.trans h1
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), ∑ p ∈ codes N a b L ij.1 ij.2,
        infiniteJointMoment L {p.1.1, p.1.2, p.2} := by
      apply sum_le_sum
      intro ij _
      have hh := sum_image_le_of_nonneg (s := codes N a b L ij.1 ij.2) (g := encode)
        (f := fun p ↦ infiniteJointMoment L (insert p.2 p.1))
        (fun p _ ↦ infiniteJointMoment_nonneg L _)
      simpa only [encode_joint] using hh
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1),
        (FixedChannelAlignedTargetMass.mass N a b L ij.1 ij.2 + CompressedNonalignedInteractionMass.mass N a b L ij.1 ij.2) := by
      exact sum_le_sum fun ij _ ↦ GraphStarWeights.sum_union_le_nonneg _ _ _ (fun p ↦ infiniteJointMoment_nonneg L _)
    _ = _ := sum_add_distrib

theorem finite_mass {N H a b L : ℕ} (hL : 0 < L) {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    GoodEdgePositivePalm.mass N H a b L G ≤
      beta N H a b L * (∑ z ∈ G, |infiniteMarginal z L - (2 ^ L : ℝ)⁻¹|) +
        FixedChannelAlignedTargetMass.channelMass N a b L +
          CompressedNonalignedInteractionMass.channelMass N a b L := by
  have h0 := finite_split N H a b L hL G
  have h1 := crossing_bound (H := H) (a := a) (b := b) (L := L) hG
  linarith only [h0, h1]

end PaperP1.GoodEdgeFullPalm
