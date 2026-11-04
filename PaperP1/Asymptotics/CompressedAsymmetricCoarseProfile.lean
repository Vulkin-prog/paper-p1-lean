module

public import PaperP1.Asymptotics.ExpandedAsymmetricCoarseProfileUnderInputs
public import PaperP1.Arithmetic.CompressedTargetCenters

/-! # The coarse asymmetric profile for actual compressed source pairs

For each pair of unit offsets the compressed anchor is injective. It lies
in a fixed expanded old-centre interval, while the new centre stays dyadic.
The bound is therefore uniform over the actual compressed blocks, and
does not assume a profile estimate for those blocks as a new input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedAsymmetricCoarseProfile

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.DyadicEndpointPairs
  PaperP1.CompressedSourceBlocks PaperP1.AsymmetricCoarseProfileUnderInputs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def points (N a b L : ℕ) (i j : Fin (L + 1)) : Finset ((ℕ × ℕ) × ℕ) :=
  (sourcePairs N a b L i j ×ˢ dyadicBlock N).filter fun p ↦
    ¬CompressedTargetAlignment.Aligned b (anchor b L i p.1) p.2 L

def centreMap (b L : ℕ) (i : Fin (L + 1)) (p : (ℕ × ℕ) × ℕ) : ℕ × ℕ :=
  (anchor b L i p.1, p.2)

def profile (N a b L H : ℕ) (i j : Fin (L + 1)) : ℝ :=
  ∑ p ∈ points N a b L i j,
    weight H L (CompressedSourceBlocks.block N a b L i j) (centreMap b L i p)

def channelProfile (N a b L H : ℕ) : ℝ :=
  ∑ ij : Fin (L + 1) × Fin (L + 1), profile N a b L H ij.1 ij.2

theorem anchor_mem_expanded {N a b L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hb : 2 ≤ b)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    anchor b L i xy ∈ ExpandedAsymmetricSupportEnvelope.block N (3 * b) := by
  have hx := (mem_sourcePairs.mp hxy).1
  have hxlo := (mem_Ico.mp hx).1
  have hxpos : 0 < xy.1 := by omega
  have hvlo : N - 1 ≤ startCompleteVertexLabel xy.1 L i := by
    rw [startCompleteVertexLabel_eq_offset hxpos]
    omega
  have hvhi : startCompleteVertexLabel xy.1 L i ≤ 3 * N := by
    exact_mod_cast (OriginalWindowValueBounds.values_geometry N L xy.1 hN (mem_Ico.mp hx) hLN
      (startCompleteVertexLabel xy.1 L i) (NormalizedWindowSets.mem_values.mpr ⟨i, rfl⟩)).1.2
  have hlo := Nat.mul_le_mul hb hvlo
  have hhi := Nat.mul_le_mul_left b hvhi
  apply mem_Ico.mpr
  change N ≤ b * startCompleteVertexLabel xy.1 L i ∧
    b * startCompleteVertexLabel xy.1 L i < N + (3 * b) * N
  constructor
  · exact (show N ≤ 2 * (N - 1) by omega).trans hlo
  · nlinarith only [hhi, hN]

theorem finite_bound {N a b L H : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 2 ≤ b)
    (hLN : L ≤ N) (i j : Fin (L + 1)) :
    profile N a b L H i j ≤ ExpandedAsymmetricCoarseProfileUnderInputs.profile N (3 * b) L H b
      (CompressedSourceBlocks.block N a b L i j) := by
  have hbpos : 0 < b := by omega
  let P := points N a b L i j
  let w := weight H L (CompressedSourceBlocks.block N a b L i j)
  have hinj : Set.InjOn (centreMap b L i) (P : Set ((ℕ × ℕ) × ℕ)) := by
    intro p hp q hq heq
    have hx := congrArg Prod.fst heq
    have hz := congrArg Prod.snd heq
    have hpS := (mem_product.mp (mem_filter.mp hp).1).1
    have hqS := (mem_product.mp (mem_filter.mp hq).1).1
    have hpq : p.1 = q.1 := first_anchor_injective (by omega) ha hbpos i j hpS hqS hx
    exact Prod.ext hpq hz
  have hmap : P.image (centreMap b L i) ⊆
      ExpandedAsymmetricCoarseProfileUnderInputs.nonalignedPairs N (3 * b) L b := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hpD, hnon⟩ := mem_filter.mp hp
    obtain ⟨hpS, hpz⟩ := mem_product.mp hpD
    exact mem_filter.mpr ⟨mem_product.mpr ⟨anchor_mem_expanded hN hLN hb i j hpS, hpz⟩, hnon⟩
  change (∑ p ∈ P, w (centreMap b L i p)) ≤ _
  rw [← sum_image hinj]
  exact sum_le_sum_of_subset_of_nonneg hmap (fun q _ _ ↦ weight_nonneg H L _ q)

theorem uniform_offsets (a b Dcut : ℕ) (ha : 0 < a) (hab : a ≤ b) (hb : 2 ≤ b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg (AsymmetricComponentHostCount.sizeCap Dcut (ε / 8)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (2 * b + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ i j : Fin (L + 1), profile N a b L H i j ≤ (N : ℝ) ^ (4 / 3 + ε)) := by
  obtain ⟨Ds, kg, ko, K, hDs, hK, hp⟩ := ExpandedAsymmetricCoarseProfileUnderInputs.uniform_profile
    (3 * b) (by omega) C ε b Dcut (by omega) hε
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨Np, _hNp, hp⟩ := hp hCoverG hCoverO hCurveG hCurveO
  refine ⟨max 4 (max Np Ng), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh i j
  have hLN : L ≤ N := by have hh := (hg N (by omega) L hcrit).2.2.2.1; omega
  refine (finite_bound (by omega) ha hb hLN i j).trans ?_
  apply hp N (by omega) L H hcrit hHlow hHhigh (CompressedSourceBlocks.block N a b L i j)
  intro X _hX n hn
  have hh := CompressedTargetCenters.block_width (by omega : 0 < N) hab i j hn
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hh

theorem uniform_channel (a b Dcut : ℕ) (ha : 0 < a) (hab : a ≤ b) (hb : 2 ≤ b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds kg ko K : ℕ, 0 < Ds ∧ 1 ≤ K ∧
      (UniformSourceSurfaceCover.UniformCover kg (AsymmetricComponentHostCount.sizeCap Dcut (ε / 16)) Ds →
      UniformOrdinarySurfaceCover.UniformCover ko (K + 1) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + kg) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (ko + 3) M) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (2 * b + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      channelProfile N a b L H ≤ (N : ℝ) ^ (4 / 3 + ε)) := by
  obtain ⟨Ds, kg, ko, K, hDs, hK, hc⟩ := uniform_offsets a b Dcut ha hab hb C (ε / 2) (by positivity)
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nw, hw⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le 1 2 (ε / 2) (by positivity)
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨Nc, _hNc, hc⟩ := hc (by simpa only [div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hCoverG)
    hCoverO hCurveG hCurveO
  refine ⟨max 4 (max Nc (max Ns Nw)), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L + 1 : ℝ) ^ 2), Nat.cast_add, Nat.cast_one] using
      hw N (by omega) L (hs N (by omega) L hcrit).2
  calc
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (N : ℝ) ^ (4 / 3 + ε / 2) :=
      sum_le_sum (fun ij _ ↦ hc N (by omega) L H hcrit hHlow hHhigh ij.1 ij.2)
    _ = ((L + 1 : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (4 / 3 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, pow_two]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (4 / 3 + ε / 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos, show ε / 2 + (4 / 3 + ε / 2) = 4 / 3 + ε by ring]

end PaperP1.CompressedAsymmetricCoarseProfile
