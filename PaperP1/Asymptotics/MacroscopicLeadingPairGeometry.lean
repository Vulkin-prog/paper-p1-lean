module

public import PaperP1.Arithmetic.ExactUnitGeometric
public import PaperP1.Asymptotics.MacroscopicChannelPartition
public import PaperP1.Asymptotics.MacroscopicLeadingUnitSums

/-! # Actual leading-pair orientation and rational support identities

All enlarged1:2 pairs, including zero-unit pairs, are eventually separated.
Both orders form a disjoint union and every actual rational unit sum is
supported on this literal geometric channel.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicLeadingPairGeometry

open Finset PaperP1.Arithmetic PaperP1.NormalizedUnitCount PaperP1.EnlargedPairGeometry
  PaperP1.MacroscopicIntervalGeometry PaperP1.MacroscopicFixedChannelComparison
  PaperP1.MacroscopicChannelPartition PaperP1.PrivateUnitCovariance
  PaperP1.UnsignedUnitFourierAggregate PaperP1.MacroscopicLeadingUnitSums

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem geometric_separated {x y L : ℕ} (hlarge : 5 * (L + 1) < x) (hg : Geometric 1 2 x y L) :
    x + L < y := by
  have hh := (abs_le.mp hg).2
  have hx : (5 : ℤ) * ((L + 1 : ℕ) : ℤ) < x := by exact_mod_cast hlarge
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_mul] at hh hx
  have hi : (x : ℤ) + L < y := by omega
  exact_mod_cast hi

theorem uniform_separation (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → ∀ xy ∈ channelPairs M δ 1 2 L, xy.1 + L < xy.2 := by
  obtain ⟨M₀, h⟩ := PaperP1.MacroscopicPolynomialScale.polynomial_lt_source C δ 5 hδ (by norm_num) 1
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit xy hxy
  obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
  have hx := (mem_product.mp hblock).1
  have hh := h M hM L hcrit xy.1 hx
  simp only [pow_one] at hh
  exact geometric_separated (by exact_mod_cast hh) hg

theorem uniform_symmetric_sum (C δ : ℝ) (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      leading M δ L = channelPairs M δ 1 2 L ∪ channelPairs M δ 2 1 L ∧
      Disjoint (channelPairs M δ 1 2 L) (channelPairs M δ 2 1 L) ∧
      ∀ f : ℕ × ℕ → ℝ, (∀ xy, f xy = f xy.swap) →
        (∑ xy ∈ leading M δ L, f xy) = 2 * ∑ xy ∈ channelPairs M δ 1 2 L, f xy := by
  obtain ⟨M₀, h⟩ := uniform_separation C δ hδ
  refine ⟨M₀, ?_⟩
  intro M hM L hcrit
  have hf := h M hM L hcrit
  have hr : ∀ xy ∈ channelPairs M δ 2 1 L, xy.2 + L < xy.1 := by
    intro xy hxy
    have hswap : xy.swap ∈ channelPairs M δ 1 2 L := by
      obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
      obtain ⟨hx, hy⟩ := mem_product.mp hblock
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, (geometric_swap 2 1 xy.1 xy.2 L).mp hg⟩
    exact hf xy.swap hswap
  have heq : leading M δ L = channelPairs M δ 1 2 L ∪ channelPairs M δ 2 1 L := by
    apply filter_eq_self.mpr
    intro xy hxy
    rcases mem_union.mp hxy with hxy | hxy
    · have hh := hf xy hxy
      unfold Nat.dist
      omega
    · have hh := hr xy hxy
      unfold Nat.dist
      omega
  have hdis : Disjoint (channelPairs M δ 1 2 L) (channelPairs M δ 2 1 L) := by
    apply disjoint_left.mpr
    intro xy hxy hyx
    have hh := hf xy hxy
    have hk := hr xy hyx
    omega
  refine ⟨heq, hdis, ?_⟩
  intro f hsym
  have hsum : (∑ xy ∈ channelPairs M δ 2 1 L, f xy) = ∑ xy ∈ channelPairs M δ 1 2 L, f xy := by
    rw [← channel_swap M 1 2 L δ, sum_image]
    · exact sum_congr rfl (fun xy _ ↦ (hsym xy).symm)
    · intro xy _ uv _ hh
      have hk := congrArg Prod.swap hh
      simpa only [Prod.swap_swap] using hk
  rw [heq, sum_union hdis, hsum]
  ring

theorem rational_forward_sums {M L : ℕ} {δ : ℝ} (hM : 2 ≤ M) (hδ : 0 < δ) :
    (∑ xy ∈ channelPairs M δ 1 2 L, unitWeight 1 2 xy.1 xy.2 L) =
      ∑ x ∈ starts M δ, ∑ y ∈ starts M δ, unitWeight 1 2 x y L ∧
    (∑ xy ∈ channelPairs M δ 1 2 L, signedUnitSum 1 2 xy.1 xy.2 L) =
      ∑ x ∈ starts M δ, ∑ y ∈ starts M δ, signedUnitSum 1 2 x y L := by
  have hz : ∀ xy ∈ (starts M δ) ×ˢ (starts M δ), xy ∉ channelPairs M δ 1 2 L →
      (PaperP1.NormalizedUnitCount.units 1 2 xy.1 xy.2 L).card = 0 := by
    intro xy hblock hn
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    apply card_eq_zero.mpr
    apply not_nonempty_iff_eq_empty.mp
    intro hu
    exact hn (mem_filter.mpr ⟨hblock, PaperP1.ExactUnitGeometric.of_nonempty
      (by have := starts_pos hM hδ hx; omega) (by have := starts_pos hM hδ hy; omega) hu⟩)
  constructor
  · rw [← sum_product (starts M δ) (starts M δ) (fun xy : ℕ × ℕ ↦ unitWeight 1 2 xy.1 xy.2 L)]
    apply sum_subset (filter_subset _ _)
    intro xy hxy hn
    exact unitWeight_zero_of_card_le_one (by rw [hz xy hxy hn]; omega)
  · rw [← sum_product (starts M δ) (starts M δ) (fun xy : ℕ × ℕ ↦ signedUnitSum 1 2 xy.1 xy.2 L)]
    apply sum_subset (filter_subset _ _)
    intro xy hxy hn
    exact PaperP1.UnitFourierWeight.signed_unit_sum_zero_of_card_le_one (by rw [hz xy hxy hn]; omega)

end PaperP1.MacroscopicLeadingPairGeometry
