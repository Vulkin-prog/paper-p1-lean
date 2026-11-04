module

public import PaperP1.Asymptotics.RestrictedAsymmetricProfileUnderInputs
public import PaperP1.Asymptotics.CompressedNonalignedInteractionMass
public import PaperP1.Asymptotics.CompressedChannelTargetCount

/-! # The asymmetric weight restricted to actual effective pair/target crossings

The N^(1+epsilon) host bound is derived from the original windows.
This does not assert a sharper bound for the larger raw-loss population.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualCompressedCrossingProfile

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CompressedSourceBlocks PaperP1.DyadicEndpointPairs PaperP1.AsymmetricJointWeight

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def profile (N a b L H : ℕ) (i j : Fin (L + 1)) : ℝ :=
  ∑ p ∈ CompressedNonalignedInteractionMass.points N a b L i j,
    AsymmetricCoarseProfileUnderInputs.weight H L (block N a b L i j) (CompressedAsymmetricCoarseProfile.centreMap b L i p)

def channelProfile (N a b L H : ℕ) : ℝ :=
  ∑ ij : Fin (L + 1) × Fin (L + 1), profile N a b L H ij.1 ij.2

theorem points_subset_targets (N a b L : ℕ) (i j : Fin (L + 1)) :
    CompressedNonalignedInteractionMass.points N a b L i j ⊆ CompressedChannelTargetHosts.sourceTargets N a b L i j := by
  intro p hp
  obtain ⟨hpP, _hzx, _hzy, hcross⟩ := mem_filter.mp hp
  obtain ⟨hpD, _hnon⟩ := mem_filter.mp hpP
  refine mem_filter.mpr ⟨hpD, ?_⟩
  rw [IndependentTargetDeficit.target_pair]
  intro hh
  have hz : crossRank p.1.1 p.1.2 p.2 L = 0 := by rw [crossRank, inf_comm, hh, finrank_bot]
  omega

theorem finite_bound {N a b L H : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b)
    (hL : 0 < L) (i j : Fin (L + 1)) (A : ℝ)
    (hcap : ∀ xy ∈ sourcePairs N a b L i j, ∀ z ∈ dyadicBlock N,
      infiniteJointMoment L {xy.1, xy.2} * infiniteMarginal z L ≤ A) :
    CompressedNonalignedInteractionMass.mass N a b L i j ≤ 2 * A * profile N a b L H i j := by
  let P := CompressedNonalignedInteractionMass.points N a b L i j
  let w := fun p : (ℕ × ℕ) × ℕ ↦ AsymmetricCoarseProfileUnderInputs.weight H L
    (block N a b L i j) (CompressedAsymmetricCoarseProfile.centreMap b L i p)
  have hpoint : ∀ p ∈ P, infiniteJointMoment L {p.1.1, p.1.2, p.2} ≤ 2 * A * w p := by
    intro p hp
    obtain ⟨hpP, hzx, hzy, hcross⟩ := mem_filter.mp hp
    obtain ⟨hpD, _hnon⟩ := mem_filter.mp hpP
    obtain ⟨hxy, hz⟩ := mem_product.mp hpD
    have hnonneg : 0 ≤ w p := AsymmetricCoarseProfileUnderInputs.weight_nonneg H L _ _
    have hh := compressed_crossing (H := H) hN ha hb hL i j hxy p.2 hzx hzy hcross
    have hbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcap p.1 hxy p.2 hz) (by norm_num : (0 : ℝ) ≤ 2)) hnonneg
    exact hh.trans hbound
  calc
    _ ≤ ∑ p ∈ P, 2 * A * w p := sum_le_sum hpoint
    _ = 2 * A * ∑ p ∈ P, w p := (mul_sum _ _ _).symm
    _ = _ := rfl

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
      ∀ i j : Fin (L + 1), profile N a b L H i j ≤ (N : ℝ) ^ (1 + ε)) := by
  obtain ⟨Ds, kg, ko, K, hDs, hK, hu⟩ := RestrictedAsymmetricProfileUnderInputs.uniform_weight
    (3 * b) (by omega) C ε b Dcut (by omega) hε
  obtain ⟨NC, _hNC, hc⟩ := CompressedChannelTargetCount.fixed_offsets a b ha hab C (ε / 8) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨NU, _hNU, hU⟩ := hu hCoverG hCoverO hCurveG hCurveO
  refine ⟨max 4 (max NC (max NG NU)), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh i j
  have hLN : L ≤ N := by have hh := (hg N (by omega) L hcrit).2.2.2.1; omega
  let P := CompressedNonalignedInteractionMass.points N a b L i j
  let f := CompressedAsymmetricCoarseProfile.centreMap b L i
  have hsub : P ⊆ CompressedChannelTargetHosts.sourceTargets N a b L i j := points_subset_targets N a b L i j
  have hinj : Set.InjOn f P := fun _ hp _ hq heq ↦
    CompressedChannelTargetHosts.host_key_injective (by omega) ha (by omega) i j (hsub hp) (hsub hq) heq
  change (∑ p ∈ P, AsymmetricCoarseProfileUnderInputs.weight H L (block N a b L i j) (f p)) ≤ _
  rw [← sum_image hinj]
  apply hU N (by omega) L H hcrit hHlow hHhigh (block N a b L i j)
  · intro X _hX n hn
    have hh := CompressedTargetCenters.block_width (by omega : 0 < N) hab i j hn
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hh
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨hpP, _⟩ := mem_filter.mp hp
    obtain ⟨hpD, _⟩ := mem_filter.mp hpP
    obtain ⟨hpS, hz⟩ := mem_product.mp hpD
    exact ⟨CompressedAsymmetricCoarseProfile.anchor_mem_expanded (by omega) hLN hb i j hpS, hz⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    exact (mem_filter.mp (mem_filter.mp hp).1).2
  · exact (show ((P.image f).card : ℝ) ≤ P.card by exact_mod_cast card_image_le).trans
      ((show (P.card : ℝ) ≤ (CompressedChannelTargetHosts.sourceTargets N a b L i j).card by exact_mod_cast card_le_card hsub).trans
        (hc N (by omega) L hcrit i j))

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
      channelProfile N a b L H ≤ (N : ℝ) ^ (1 + ε)) := by
  obtain ⟨Ds, kg, ko, K, hDs, hK, hu⟩ := uniform_offsets a b Dcut ha hab hb C (ε / 2) (by positivity)
  obtain ⟨NS, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow
    (CriticalBandScale.upperScale ^ 2) 2 (ε / 2) (by positivity)
  refine ⟨Ds, kg, ko, K, hDs, hK, ?_⟩
  intro hCoverG hCoverO hCurveG hCurveO
  obtain ⟨NU, _hNU, hU⟩ := hu (by simpa only [div_div, show (2 : ℝ) * 8 = 16 by norm_num] using hCoverG) hCoverO hCurveG hCurveO
  refine ⟨max 4 (max NS (max NP NU)), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (CriticalBandScale.upperScale * Real.log N) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (hs N (by omega) L hcrit).2 2
      _ = CriticalBandScale.upperScale ^ 2 * (Real.log N) ^ 2 := mul_pow _ _ _
      _ ≤ _ := by simpa only [Real.rpow_two] using hp N (by omega)
  calc
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (N : ℝ) ^ (1 + ε / 2) :=
      sum_le_sum (fun ij _ ↦ hU N (by omega) L H hcrit hHlow hHhigh ij.1 ij.2)
    _ = ((L + 1 : ℕ) : ℝ) ^ 2 * (N : ℝ) ^ (1 + ε / 2) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, pow_two]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) := mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.ActualCompressedCrossingProfile
