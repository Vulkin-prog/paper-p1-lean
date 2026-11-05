module

public import PaperP1.Asymptotics.DenseNonalignedPairs
public import PaperP1.Asymptotics.OriginalPairHosts
public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Model.CriticalPairLossComparison

/-! # Unconditional weighted nonaligned residuals for the full arithmetic source rank

The large-intersection population is counted by actual dense confinement. The
remaining positive-loss population uses the proved support count and small rank.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedSourceResidual

open Polynomial Finset PaperP1.Model PaperP1.NormalizedPairRankLoss PaperP1.FreeComponentRank

def separatedNonalignedPairs (N L : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦
    (p.1 + L < p.2 ∨ p.2 + L < p.1) ∧ ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L

theorem uniform_weighted_hosts (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∑ p ∈ F, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤ (N : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨ND, _hND, hd⟩ := DenseNonalignedPairs.uniform_kernel_hosts C (ε / 16) (ε / 4)
    (by positivity) (by positivity)
  obtain ⟨NH, _hNH, hh⟩ := OriginalPairHosts.uniform_count C (ε / 4) (by positivity)
  obtain ⟨NR, _hNR, hr⟩ := CriticalPairLossComparison.uniform_bound C
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.power_of_rank C 0 2 (ε / 4) (by norm_num) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (4 * (2 : ℝ) ^ C + 1)
    (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨2 + ND + NH + NR + NP + NA, by omega, ?_⟩
  intro N hN L hband F hdyadic hnon
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := F.filter fun p ↦ 0 < pairLoss p.1 p.2 L
  let S := P.filter fun p ↦ (ε / 16) * L ≤ (pairIntersectionRank p.1 p.2 L : ℝ)
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
  have hScard : (S.card : ℝ) ≤ (N : ℝ) ^ (ε / 4) := by
    apply hd N (by omega) L hband S (fun p hpS ↦ hdyadic p (hSF hpS))
      (fun p hpS ↦ hnon p (hSF hpS))
    intro p hpS
    rw [TwoTargetEmptySource.dimension]
    exact (mem_filter.mp hpS).2
  have hweightS (p : ℕ × ℕ) (hpS : p ∈ S) :
      (2 ^ pairLoss p.1 p.2 L : ℝ) - 1 ≤ (4 * (2 : ℝ) ^ C) * N := by
    have hloss := (hr N (by omega) L hband p.1 (hdyadic p (hSF hpS)).1
      p.2 (hdyadic p (hSF hpS)).2).2
    have hw := CriticalChannelPowers.word_upper (by omega : 2 ≤ N) hband
    calc
      _ ≤ (2 ^ pairLoss p.1 p.2 L : ℝ) := sub_le_self _ zero_le_one
      _ ≤ (2 : ℝ) ^ (L + 2) := pow_le_pow_right₀ (by norm_num) hloss
      _ = 4 * (2 ^ L : ℝ) := by rw [pow_add]; norm_num; ring
      _ ≤ 4 * ((2 : ℝ) ^ C * N) := mul_le_mul_of_nonneg_left hw (by norm_num)
      _ = _ := by ring
  have hS : (∑ p ∈ S, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
      (4 * (2 : ℝ) ^ C) * (N : ℝ) ^ (1 + ε / 2) := by
    calc
      _ ≤ ∑ _p ∈ S, (4 * (2 : ℝ) ^ C) * N := sum_le_sum hweightS
      _ = (S.card : ℝ) * ((4 * (2 : ℝ) ^ C) * N) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ (ε / 4) * ((4 * (2 : ℝ) ^ C) * N) :=
        mul_le_mul_of_nonneg_right hScard (by positivity)
      _ = (4 * (2 : ℝ) ^ C) * (N : ℝ) ^ (1 + ε / 4) := by
        rw [Real.rpow_add hn, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (by positivity)
  have hTsub : T ⊆ PairHostCover.hosts N L := by
    intro p hpT
    have hpP := (mem_sdiff.mp hpT).1
    exact mem_filter.mpr ⟨mem_product.mpr (hdyadic p (hPF hpP)), (mem_filter.mp hpP).2⟩
  have hTcard : (T.card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 4) :=
    (show (T.card : ℝ) ≤ (PairHostCover.hosts N L).card by exact_mod_cast card_le_card hTsub).trans
      (hh N (by omega) L hband)
  have hweightT (p : ℕ × ℕ) (hpT : p ∈ T) :
      (2 ^ pairLoss p.1 p.2 L : ℝ) - 1 ≤ (N : ℝ) ^ (ε / 4) := by
    obtain ⟨hpP, hpS⟩ := mem_sdiff.mp hpT
    have hdsmall : (pairIntersectionRank p.1 p.2 L : ℝ) < (ε / 16) * L := by
      by_contra h
      exact hpS (mem_filter.mpr ⟨hpP, le_of_not_gt h⟩)
    have hloss : (pairLoss p.1 p.2 L : ℝ) ≤ (pairIntersectionRank p.1 p.2 L : ℝ) + 2 := by
      exact_mod_cast (hr N (by omega) L hband p.1 (hdyadic p (hTF hpT)).1
        p.2 (hdyadic p (hTF hpT)).2).1
    have hpow := hp N (by omega) L (pairLoss p.1 p.2 L) hband (by
      push_cast
      nlinarith only [hdsmall.le, hloss, Nat.cast_nonneg (α := ℝ) L, hε.le])
    exact (sub_le_self _ zero_le_one).trans (by simpa only [zero_add] using hpow)
  have hT : (∑ p ∈ T, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤ (N : ℝ) ^ (1 + ε / 2) := by
    calc
      _ ≤ ∑ _p ∈ T, (N : ℝ) ^ (ε / 4) := sum_le_sum hweightT
      _ = (T.card : ℝ) * (N : ℝ) ^ (ε / 4) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ (1 + ε / 4) * (N : ℝ) ^ (ε / 4) :=
        mul_le_mul_of_nonneg_right hTcard (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hpartition := sum_sdiff (f := fun p ↦ ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1))
    (show S ⊆ P from filter_subset _ _)
  change (∑ p ∈ T, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) +
    (∑ p ∈ S, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) = _ at hpartition
  have htotal : (∑ p ∈ F, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
      (4 * (2 : ℝ) ^ C + 1) * (N : ℝ) ^ (1 + ε / 2) := by
    linarith only [hsumP, hpartition, hS, hT]
  exact htotal.trans (by convert ha N (by omega) using 1; congr 1; ring)

theorem uniform_source_bounds (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((OriginalPairHosts.separatedHosts N L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧
      (∑ p ∈ separatedNonalignedPairs N L, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
        (N : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨NH, _hNH, hh⟩ := OriginalPairHosts.uniform_count C ε hε
  obtain ⟨NW, _hNW, hw⟩ := uniform_weighted_hosts C ε hε
  refine ⟨2 + NH + NW, by omega, ?_⟩
  intro N hN L hband
  constructor
  · have hc : ((OriginalPairHosts.separatedHosts N L).card : ℝ) ≤ (PairHostCover.hosts N L).card := by
      exact_mod_cast card_le_card (OriginalPairHosts.separated_subset N L)
    exact hc.trans (hh N (by omega) L hband)
  · exact hw N (by omega) L hband (separatedNonalignedPairs N L)
      (fun _ hp ↦ mem_product.mp (mem_filter.mp hp).1)
      (fun _ hp ↦ (mem_filter.mp hp).2.2)

theorem article_3_2 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((OriginalPairHosts.separatedHosts N L).card : ℝ) ≤ (N : ℝ) ^ (6 / 5 + ε) ∧
      (∑ p ∈ separatedNonalignedPairs N L, ((2 ^ pairLoss p.1 p.2 L : ℝ) - 1)) ≤
        (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_source_bounds C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : (N : ℝ) ^ (1 + ε) ≤ (N : ℝ) ^ (6 / 5 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  exact ⟨(h N hN L hband).1.trans hp, (h N hN L hband).2.trans hp⟩

end PaperP1.NonalignedSourceResidual
