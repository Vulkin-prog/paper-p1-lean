module

public import PaperP1.Model.UnitFourierWeight
public import PaperP1.Arithmetic.FixedChannelSourceGeometry
public import PaperP1.Arithmetic.NormalizedDefectSources

/-! # The actual retained private channel family, including probability-zero pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateChannelSources

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount PaperP1.GoodEdgeCompression
  PaperP1.FixedChannelSourceGeometry PaperP1.DyadicEndpointPairs PaperP1.PrivateUnitCovariance

local instance privateChannelSourcePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def goodSources (N H a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦
    2 ≤ (units a b xy.1 xy.2 L).card ∧ PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b xy.1 xy.2 L)

def channelSources (N H a b L : ℕ) : Finset (ℕ × ℕ) :=
  goodSources N H a b L ∪ (goodSources N H a b L).image Prod.swap

def forwardMass (N H a b L : ℕ) : ℝ := ∑ xy ∈ goodSources N H a b L, infiniteJointMoment L {xy.1, xy.2}

def channelMass (N H a b L : ℕ) : ℝ := ∑ xy ∈ channelSources N H a b L, infiniteJointMoment L {xy.1, xy.2}

theorem mem_goodSources {N H a b L : ℕ} {xy : ℕ × ℕ} :
    xy ∈ goodSources N H a b L ↔ xy.1 ∈ dyadicBlock N ∧ xy.2 ∈ dyadicBlock N ∧
      2 ≤ (units a b xy.1 xy.2 L).card ∧ PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b xy.1 xy.2 L) := by
  simp only [goodSources, mem_filter, mem_product, and_assoc]

theorem good_sources_subset_unitSources (N H a b L : ℕ) : goodSources N H a b L ⊆ unitSources N a b L := by
  intro xy hxy
  obtain ⟨hx, hy, hc, _⟩ := mem_goodSources.mp hxy
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, card_pos.mp (by omega)⟩

theorem good_sources_card {N H a b L : ℕ} (hN : 0 < N) (ha : 0 < a) :
    (goodSources N H a b L).card ≤ (L + 1) ^ 2 * N :=
  (card_le_card (good_sources_subset_unitSources N H a b L)).trans (unit_sources_card hN ha)

theorem good_sources_order {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) {xy : ℕ × ℕ} (hxy : xy ∈ goodSources N H a b L) : xy.1 < xy.2 := by
  obtain ⟨hx, hy, hc, _⟩ := mem_goodSources.mp hxy
  obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (units a b xy.1 xy.2 L).card)
  exact ActualSourceTranslations.source_pair_order (by omega) hab hlarge u.1 u.2
    (mem_sourcePairs.mpr ⟨hx, hy, mem_units.mp hu⟩)

theorem good_sources_separated {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    {xy : ℕ × ℕ} (hxy : xy ∈ goodSources N H a b L) : xy.1 + L ≤ xy.2 := by
  obtain ⟨hx, hy, hc, _⟩ := mem_goodSources.mp hxy
  obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (units a b xy.1 xy.2 L).card)
  exact source_separated hN ha hab hcop hlarge u.1 u.2 (mem_sourcePairs.mpr ⟨hx, hy, mem_units.mp hu⟩)

theorem orientation_disjoint {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) :
    Disjoint (goodSources N H a b L) ((goodSources N H a b L).image Prod.swap) := by
  apply disjoint_left.mpr
  intro xy hxy hswap
  obtain ⟨uv, huv, heq⟩ := mem_image.mp hswap
  have hforward := good_sources_order hN hab hlarge hxy
  have hback := good_sources_order hN hab hlarge huv
  rw [← heq] at hforward
  change uv.2 < uv.1 at hforward
  omega

theorem channel_mass_twice_forward {N H a b L : ℕ} (hN : 2 ≤ N) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) : channelMass N H a b L = 2 * forwardMass N H a b L := by
  unfold channelMass channelSources
  rw [sum_union (orientation_disjoint hN hab hlarge), sum_image]
  · have heq : (∑ xy ∈ goodSources N H a b L, infiniteJointMoment L {xy.2, xy.1}) = forwardMass N H a b L := by
      unfold forwardMass
      apply sum_congr rfl
      intro xy _
      rw [pair_comm]
    change forwardMass N H a b L +
      (∑ xy ∈ goodSources N H a b L, infiniteJointMoment L {xy.2, xy.1}) = _
    rw [heq]
    ring
  · intro xy _ uv _ heq
    have h := congrArg Prod.swap heq
    simpa using h

theorem forward_mass_formula {N H a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hlarge : (a + b) * (L + 1) < N) (hL : 0 < L) :
    forwardMass N H a b L = ((2 ^ L : ℝ)⁻¹) ^ 2 *
      (((goodSources N H a b L).card : ℝ) + ∑ xy ∈ goodSources N H a b L, signedUnitSum a b xy.1 xy.2 L) := by
  calc
    _ = ∑ xy ∈ goodSources N H a b L, ((2 ^ L : ℝ)⁻¹) ^ 2 * (1 + signedUnitSum a b xy.1 xy.2 L) := by
      apply sum_congr rfl
      intro xy hxy
      obtain ⟨hx, hy, _, hprivate⟩ := mem_goodSources.mp hxy
      exact private_pair_mass ha (ha.trans hab) (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1)
        (ne_of_lt (good_sources_order hN hab hlarge hxy)) hL hprivate.private
    _ = _ := by rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]

end PaperP1.PrivateChannelSources
