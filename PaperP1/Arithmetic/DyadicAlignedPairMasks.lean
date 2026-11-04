module

public import PaperP1.Asymptotics.DyadicMacroscopicTransfer
public import PaperP1.Asymptotics.MacroscopicFixedChannelComparison

/-! # Literal ordered dyadic aligned masks and polynomial endpoint hosts

All coefficient orientations and zero-unit geometric pairs are retained.
The1:2 sector is confined to the two actual dyadic endpoints.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicAlignedPairMasks

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.EnlargedPairGeometry

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channel (N L a b : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦ Geometric a b xy.1 xy.2 L

def high (N L q : ℕ) : Finset (ℕ × ℕ) :=
  ((PaperP1.BoundedGeometricPairCount.coefficients (L + 1)).filter fun ab ↦
    q ≤ max ab.1 ab.2 ∧ ab.1.Coprime ab.2).biUnion fun ab ↦ channel N L ab.1 ab.2

def separated (S : Finset (ℕ × ℕ)) (L : ℕ) : Finset (ℕ × ℕ) := S.filter fun xy ↦ L < Nat.dist xy.1 xy.2

def aligned (N L : ℕ) : Finset (ℕ × ℕ) := separated (high N L 1) L

def leading (N L : ℕ) : Finset (ℕ × ℕ) := separated (channel N L 2 3 ∪ channel N L 3 2) L

def boundary (N L : ℕ) : Finset (ℕ × ℕ) := separated (channel N L 1 2 ∪ channel N L 2 1) L

theorem channel_swap (N L a b : ℕ) : (channel N L a b).image Prod.swap = channel N L b a := by
  ext xy
  constructor
  · intro hxy
    obtain ⟨uv, huv, rfl⟩ := mem_image.mp hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp huv
    obtain ⟨hu, hv⟩ := mem_product.mp hblock
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hv, hu⟩, (geometric_swap a b uv.1 uv.2 L).mp hg⟩
  · intro hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    exact mem_image.mpr ⟨xy.swap,
      mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, (geometric_swap b a xy.1 xy.2 L).mp hg⟩, by simp⟩

theorem channel_subset_macro {N L a b : ℕ} (hN : 2 ≤ N) :
    channel N L a b ⊆ PaperP1.MacroscopicFixedChannelComparison.channelPairs (2 * N) (1 / 2) a b L := by
  intro xy hxy
  obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨PaperP1.DyadicMacroscopicTransfer.dyadic_subset hN hx, PaperP1.DyadicMacroscopicTransfer.dyadic_subset hN hy⟩, hg⟩

theorem high_subset_macro {N L q : ℕ} (hN : 2 ≤ N) :
    high N L q ⊆ PaperP1.MacroscopicHighRelationMass.highPairs (2 * N) (1 / 2) L q := by
  intro xy hxy
  obtain ⟨ab, hab, hpair⟩ := mem_biUnion.mp hxy
  exact mem_biUnion.mpr ⟨ab, hab, channel_subset_macro hN hpair⟩

theorem high_card {N L q : ℕ} (hN : 2 ≤ N) : (high N L q).card ≤ 10 * N * (L + 1) ^ 10 := by
  have hh := (card_le_card (high_subset_macro hN (L := L) (q := q))).trans
    (PaperP1.MacroscopicHighRelationMass.high_card_bound (by omega : 2 ≤ 2 * N) (by norm_num : (0 : ℝ) < 1 / 2))
  nlinarith only [hh]

theorem height_two_subset (N L : ℕ) :
    channel N L 1 2 ⊆ Icc N (N + 3 * (L + 1)) ×ˢ Icc (2 * N - 3 * (L + 1)) (2 * N) := by
  intro xy hxy
  obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
  obtain ⟨hx, hy⟩ := mem_product.mp hblock
  obtain ⟨hxlo, _hxhi⟩ := mem_Ico.mp hx
  obtain ⟨_hylo, hyhi⟩ := mem_Ico.mp hy
  have hgeomI : |(2 : ℤ) * xy.1 - xy.2| ≤ 3 * ((L + 1 : ℕ) : ℤ) := by
    simpa only [Geometric, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, one_mul] using hg
  have hh := (abs_le.mp hgeomI).2
  have heq : 2 * xy.1 ≤ xy.2 + 3 * (L + 1) := by omega
  exact mem_product.mpr ⟨mem_Icc.mpr ⟨hxlo, by omega⟩, mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem height_two_card (N L : ℕ) : (channel N L 1 2).card ≤ 16 * (L + 1) ^ 2 := by
  have hxcard : (Icc N (N + 3 * (L + 1))).card = 3 * (L + 1) + 1 := by rw [Nat.card_Icc]; omega
  have hycard : (Icc (2 * N - 3 * (L + 1)) (2 * N)).card ≤ 3 * (L + 1) + 1 := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ (Icc N (N + 3 * (L + 1)) ×ˢ Icc (2 * N - 3 * (L + 1)) (2 * N)).card := card_le_card (height_two_subset N L)
    _ ≤ (3 * (L + 1) + 1) ^ 2 := by rw [card_product, hxcard, pow_two]; exact Nat.mul_le_mul_left _ hycard
    _ ≤ (4 * (L + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by ring

theorem boundary_card (N L : ℕ) : (boundary N L).card ≤ 32 * (L + 1) ^ 2 := by
  have hinj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) := by
    intro xy uv hh
    have hk := congrArg Prod.swap hh
    simpa only [Prod.swap_swap] using hk
  have hr : (channel N L 2 1).card = (channel N L 1 2).card := by
    rw [← channel_swap N L 1 2, card_image_of_injective _ hinj]
  have hh : (boundary N L).card ≤ (channel N L 1 2).card + (channel N L 2 1).card :=
    (card_le_card (filter_subset _ _ : boundary N L ⊆ channel N L 1 2 ∪ channel N L 2 1)).trans (card_union_le _ _)
  rw [hr] at hh
  have hc := height_two_card N L
  omega

end PaperP1.DyadicAlignedPairMasks
