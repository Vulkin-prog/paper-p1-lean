module

public import PaperP1.Asymptotics.DenseSourcePairKernelUnderInputs
public import PaperP1.Asymptotics.OriginalPairHosts

/-! # A conditional N^(1+epsilon) nonaligned residual for the literal arithmetic source rank

The rank is 2L minus the joint square-class rank and includes the local kernels.
The unconditional support bound and proved sparse/dense graph decomposition
improve the printed exponent 6/5, under the same explicit geometric properties.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedSourceResidualUnderInputs

open Finset PaperP1.Model PaperP1.NormalizedPairRankLoss PaperP1.RawPairRelationRank
  PaperP1.LargePrimeGraphResolution

def separatedNonalignedPairs (N L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦
    (p.1 + L < p.2 ∨ p.2 + L < p.1) ∧ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L

theorem uniform_weighted_hosts (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 16)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∑ p ∈ F, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤ A * (N : ℝ) ^ (1 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hdense⟩ := DenseSourcePairKernelUnderInputs.uniform_source_kernel
    C (ε / 2) (ε / 16) (by positivity) (by positivity)
  obtain ⟨Ns, _hNs, hs⟩ := OriginalPairHosts.uniform_count C (ε / 4) (by positivity)
  obtain ⟨Nd, hd⟩ := CriticalPairKernelPowers.defects_small C (ε / 16) (by positivity)
  obtain ⟨Np, hp⟩ := CriticalPairKernelPowers.power_of_rank C 0 0 (ε / 4) (by norm_num) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, Nc, hc⟩ := hdense hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨A + 1, by positivity, max 2 (max Ns (max Nd (max Np Nc))), ?_⟩
  intro N hN L hcrit F hdyadic hnon
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := F.filter fun p ↦ 0 < pairLoss p.1 p.2 L
  let S := P.filter fun p ↦ (ε / 16) * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L
  let T := P \ S
  have hPF : P ⊆ F := filter_subset _ _
  have hSF : S ⊆ F := (filter_subset _ _).trans hPF
  have hTF : T ⊆ F := sdiff_subset.trans hPF
  have hsumP : (∑ p ∈ P, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) =
      ∑ p ∈ F, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1) := by
    apply sum_subset hPF
    intro p hpF hpP
    have hz : pairLoss p.1 p.2 L = 0 := by
      by_contra hn
      exact hpP (mem_filter.mpr ⟨hpF, Nat.pos_of_ne_zero hn⟩)
    simp only [hz, pow_zero, sub_self]
  have hS : (∑ p ∈ S, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤ A * (N : ℝ) ^ (1 + ε / 2) :=
    hc N (by omega) L hcrit S (fun p hpS ↦ hdyadic p (hSF hpS))
      (fun p hpS ↦ hnon p (hSF hpS)) (fun _ hpS ↦ (mem_filter.mp hpS).2)
  have hTsupport : T ⊆ PairHostCover.hosts N L := by
    intro p hpT
    have hpP := (mem_sdiff.mp hpT).1
    have hpF := hPF hpP
    exact mem_filter.mpr ⟨mem_product.mpr (hdyadic p hpF), (mem_filter.mp hpP).2⟩
  have hTcard : (T.card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 4) :=
    (show (T.card : ℝ) ≤ (PairHostCover.hosts N L).card by exact_mod_cast card_le_card hTsupport).trans
      (hs N (by omega) L hcrit)
  have hweightT : ∀ p ∈ T, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1) ≤ (N : ℝ) ^ (ε / 4) := by
    intro p hpT
    obtain ⟨hpP, hpS⟩ := mem_sdiff.mp hpT
    have hpF := hPF hpP
    have hsmall : (nontrivialComponentCount p.1 p.2 L : ℝ) < (ε / 16) * ((L + 1 : ℕ) : ℝ) := by
      by_contra hn
      exact hpS (mem_filter.mpr ⟨hpP, le_of_not_gt hn⟩)
    have hx : 1 ≤ p.1 := by have h := (mem_Ico.mp (hdyadic p hpF).1).1; omega
    have hy : 1 ≤ p.2 := by have h := (mem_Ico.mp (hdyadic p hpF).2).1; omega
    have hraw := rank_le_components (L := L) hx hy
    have hrawR : (fullRank p.1 p.2 L : ℝ) ≤ defectiveVertexCount p.1 p.2 L + nontrivialComponentCount p.1 p.2 L := by exact_mod_cast hraw
    have hdef := hd N (by omega) L hcrit p.1 (hdyadic p hpF).1 p.2 (hdyadic p hpF).2
    have hrank : (fullRank p.1 p.2 L : ℝ) ≤ (0 + (ε / 4) / 2) * ((L + 1 : ℕ) : ℝ) + 0 := by
      nlinarith only [hrawR, hsmall.le, hdef]
    have hpower := hp N (by omega) L (fullRank p.1 p.2 L) hcrit hrank
    have hsource := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (SourcePairKernelComparison.loss_le_full p.1 p.2 L)
    have hpower' : (2 ^ fullRank p.1 p.2 L : ℝ) ≤ (N : ℝ) ^ (ε / 4) := by simpa only [zero_add] using hpower
    linarith only [hsource, hpower']
  have hT := DenseWeightedSectorUnderInputs.weighted_card_bound T
    (fun p ↦ ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) (N : ℝ) 1 (1 + ε / 4) (ε / 4) hNpos
    (by simpa only [one_mul] using hTcard) hweightT
  have hexp : (1 + ε / 4) + ε / 4 = 1 + ε / 2 := by ring
  rw [hexp, one_mul] at hT
  have hpartition := sum_sdiff (f := fun p ↦ ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1))
    (show S ⊆ P from filter_subset _ _)
  change (∑ p ∈ T, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) +
    (∑ p ∈ S, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) = _ at hpartition
  have htotal : (∑ p ∈ F, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
      (A + 1) * (N : ℝ) ^ (1 + ε / 2) := by linarith only [hpartition, hsumP, hS, hT]
  exact htotal.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity))

theorem uniform_source_bounds (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 16)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (((OriginalPairHosts.separatedHosts N L).card : ℝ) ≤ A * (N : ℝ) ^ (1 + ε) ∧
        (∑ p ∈ separatedNonalignedPairs N L, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
          A * (N : ℝ) ^ (1 + ε))) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hweighted⟩ := uniform_weighted_hosts C ε hε
  obtain ⟨Ns, _hNs, hs⟩ := OriginalPairHosts.uniform_count C ε hε
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, Nw, hw⟩ := hweighted hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 1 A, lt_of_lt_of_le hA (le_max_right _ _), max 2 (max Ns Nw), by omega, ?_⟩
  intro N hN L hcrit
  classical
  have hpow := Real.rpow_nonneg (Nat.cast_nonneg N) (1 + ε)
  constructor
  · have hcard : ((OriginalPairHosts.separatedHosts N L).card : ℝ) ≤
        (PairHostCover.hosts N L).card := by exact_mod_cast card_le_card (OriginalPairHosts.separated_subset N L)
    exact (hcard.trans (hs N (by omega) L hcrit)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 A) hpow)
  · have hdyadic : ∀ p ∈ separatedNonalignedPairs N L, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N :=
      fun _ hp ↦ mem_product.mp (mem_filter.mp hp).1
    have hnon : ∀ p ∈ separatedNonalignedPairs N L, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L :=
      fun _ hp ↦ (mem_filter.mp hp).2.2
    exact (hw N (by omega) L hcrit (separatedNonalignedPairs N L) hdyadic hnon).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)

theorem article_3_2 (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 16)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (((OriginalPairHosts.separatedHosts N L).card : ℝ) ≤ A * (N : ℝ) ^ (6 / 5 + ε) ∧
        (∑ p ∈ separatedNonalignedPairs N L, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
          A * (N : ℝ) ^ (6 / 5 + ε))) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hstrong⟩ := uniform_source_bounds C ε hε
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, N₀, hN₀, hbound⟩ := hstrong hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨A, hA, N₀, hN₀, ?_⟩
  intro N hN L hcrit
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 1 + ε ≤ 6 / 5 + ε)) hA.le
  exact ⟨(hbound N hN L hcrit).1.trans hpow, (hbound N hN L hcrit).2.trans hpow⟩

end PaperP1.NonalignedSourceResidualUnderInputs
