module

public import PaperP1.Asymptotics.OriginalCompressedNonalignedMass
public import PaperP1.Asymptotics.CompressedAlignedTripleMass
public import PaperP1.Combinatorics.TwoEdgeTripleCover

/-! # Every connected triple above an actual fixed interior unit channel has four-thirds mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedCompressedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.FixedChannelSourceGeometry PaperP1.DyadicEndpointPairs
  PaperP1.CompressedSourceBlocks

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def hosts (N a b L : ℕ) : Finset (Finset ℕ) :=
  (connectedFamilies (dyadicBlock N) L 3).filter fun T ↦
    ∃ xy ∈ unitSources N a b L, ({xy.1, xy.2} : Finset ℕ) ⊆ T

def family (p : (ℕ × ℕ) × ℕ) : Finset ℕ := {p.1.1, p.1.2, p.2}

def nonalignedHosts (N a b L : ℕ) : Finset (Finset ℕ) :=
  univ.biUnion fun ij : Fin (L + 1) × Fin (L + 1) ↦
    (OriginalCompressedNonalignedMass.points N a b L ij.1 ij.2).image family

def mass (N a b L : ℕ) : ℝ := ∑ T ∈ hosts N a b L, infiniteJointMoment L T

theorem nonaligned_mass_le (N a b L : ℕ) :
    (∑ T ∈ nonalignedHosts N a b L, infiniteJointMoment L T) ≤
      OriginalCompressedNonalignedMass.channelMass N a b L := by
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1),
        ∑ T ∈ (OriginalCompressedNonalignedMass.points N a b L ij.1 ij.2).image family,
          infiniteJointMoment L T :=
      GraphStarWeights.sum_biUnion_le_nonneg univ _ _ (infiniteJointMoment_nonneg L)
    _ ≤ _ := sum_le_sum fun _ _ ↦ sum_image_le_of_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)

theorem finite_cover {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    hosts N a b L ⊆ CompressedAlignedTripleMass.hosts {(a, b)} b N L ∪ nonalignedHosts N a b L := by
  intro T hT
  obtain ⟨hTc, xy, hxy, hpair⟩ := mem_filter.mp hT
  obtain ⟨hTp, hconn⟩ := mem_filter.mp hTc
  obtain ⟨hTN, hcard⟩ := mem_powersetCard.mp hTp
  obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hxy).1
  have hxyne : xy.1 ≠ xy.2 := (PairLossWeights.unit_order (by omega) hab hlarge hxy).ne
  obtain ⟨z, hzT, hzpair, hTjoin⟩ := TwoEdgeTripleCover.third_vertex hcard (card_pair hxyne) hpair
  have hzx : z ≠ xy.1 := by
    intro he
    apply hzpair
    rw [he]
    exact mem_insert_self _ _
  have hzy : z ≠ xy.2 := by
    intro he
    apply hzpair
    rw [he]
    exact mem_insert_of_mem (mem_singleton_self _)
  have hfamily : T = {xy.1, xy.2, z} := hTjoin.trans (by
    rw [union_singleton]
    exact (insert_comm z xy.1 {xy.2}).trans (congrArg (insert xy.1) (pair_comm z xy.2)))
  obtain ⟨ij, hij⟩ := (mem_filter.mp hxy).2
  have hsource : xy ∈ sourcePairs N a b L ij.1 ij.2 :=
    mem_sourcePairs.mpr ⟨hx, hy, NormalizedUnitCount.mem_units.mp hij⟩
  by_cases halign : CompressedTargetAlignment.Aligned b (anchor b L ij.1 xy) z L
  · apply mem_union_left
    obtain ⟨t, _ht, hbaseX, _hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop
      (hN.trans (mem_Ico.mp hx).1) ij.1 ij.2 (NormalizedUnitCount.mem_units.mp hij)
    have hanchor : anchor b L ij.1 xy = a * b * t := by
      dsimp [anchor]
      rw [hbaseX]
      ring
    have hgeom := FixedChannelLinearCount.unit_alignment (a := a) (b := b) (L := L) (by omega : 0 < N) hxy
    rw [hanchor] at halign
    rw [hfamily]
    exact CompressedAlignedTripleMass.source_mem_hosts (mem_singleton_self (a, b)) (by rwa [← hfamily])
      hx hy (hTN hzT) ij.1 hbaseX hgeom halign
  · apply mem_union_right
    have hconn' : Connected L {xy.1, xy.2, z} := hfamily ▸ hconn
    have hcross := AsymmetricJointWeight.connected_crossing L xy.1 xy.2 z hzx hzy hconn'
    apply mem_biUnion.mpr
    refine ⟨ij, mem_univ _, mem_image.mpr ⟨(xy, z), ?_, hfamily.symm⟩⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hsource, hTN hzT⟩, halign⟩, hzx, hzy, hcross⟩

theorem finite_mass {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    mass N a b L ≤ CompressedAlignedTripleMass.mass {(a, b)} b N L +
      OriginalCompressedNonalignedMass.channelMass N a b L := by
  have h0 := sum_le_sum_of_subset_of_nonneg (finite_cover hN ha hab hcop hlarge)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)
  have h1 := GraphStarWeights.sum_union_le_nonneg
    (CompressedAlignedTripleMass.hosts {(a, b)} b N L) (nonalignedHosts N a b L)
    (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h2 := nonaligned_mass_le N a b L
  change mass N a b L ≤ _ at h0
  change _ ≤ CompressedAlignedTripleMass.mass {(a, b)} b N L + _ at h1
  linarith only [h0, h1, h2]

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N a b L ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Nn, _hNn, hn⟩ := OriginalCompressedNonalignedMass.uniform_mass
    a b ha hab hcop (by omega) C (ε / 2) (by positivity)
  obtain ⟨Na, _hNa, haM⟩ := CompressedAlignedTripleMass.uniform_mass {(a, b)} b
    (by intro ab hab'; have heq := mem_singleton.mp hab'; subst ab; exact ⟨ha, hab, hb2a, hcop⟩)
    C (ε / 2) (by positivity)
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Na (max Nw (max Nf Nn))), by omega, ?_⟩
  intro N hN L hcrit
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA := (haM N (by omega) L hcrit).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-41 / 30 : ℝ) + ε / 2 ≤ -4 / 3 + ε / 2))
  have hN := hn N (by omega) L hcrit
  calc
    _ ≤ 2 * (N : ℝ) ^ (-4 / 3 + ε / 2) := by
      have hh := finite_mass (by omega : 2 ≤ N) ha hab hcop hlarge
      linarith only [hh, hA, hN]
    _ ≤ _ := by
      simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)

end PaperP1.ConnectedCompressedTripleMass
