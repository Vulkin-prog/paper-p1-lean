module

public import PaperP1.Asymptotics.UniformPairClassDeficit
public import PaperP1.Asymptotics.GoodPairSeedTail
public import PaperP1.Asymptotics.PairDeficitBounds

/-! # The literal pair deficit over every cardinality without unproved inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairDeficit

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.AllPairExtensionDeficit PaperP1.FiniteGoodChannelPartition PaperP1.PairExtensionSeedTail
  PaperP1.PairDeficitBounds

theorem article_15_9 (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        AllPairExtensionDeficit.deficit (dyadicBlock N) L u ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  let δ := ε / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let M := 2 * (2 : ℝ) ^ C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨Q, _hQ, hp⟩ := partition_inputs δ hδ
  obtain ⟨NP, _hNP, hpart⟩ := hp C δ hδ
  obtain ⟨s, _hs, NT, _hNT, ht⟩ := GoodPairSeedTail.uniform_large_seeds Q u C δ hu hδ
  obtain ⟨NF, _hNF, hf⟩ := finite_orders s u C δ hu.le hδ
  let K := ∑ k ∈ Ico 1 s, u ^ k
  have hK : 0 ≤ K := sum_nonneg fun k _ ↦ pow_nonneg hu.le k
  let A := 2 + Real.exp (u * M) * (K + 1)
  obtain ⟨NI, _hNI, hi⟩ := UniformPairClassDeficit.uniform_bound u C δ hu hδ
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption A (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NT + NI + NM + NG + NA + NP + NF, by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let H := 2 * Q * (L + 1)
  let P := (N : ℝ) ^ (-3 / 2 + ε / 2)
  have hP : 0 ≤ P := Real.rpow_nonneg hn.le _
  have hgoodsub : good Q N H L ⊆ (dyadicBlock N).powersetCard 2 :=
    fun e he ↦ (mem_filter.mp (good_subset Q N H L he)).1
  have hweaksub : weak Q N H L ⊆ (dyadicBlock N).powersetCard 2 :=
    fun e he ↦ (mem_filter.mp (mem_inter.mp (mem_sdiff.mp he).1).1).1
  have hexsub : exceptional Q N H L ⊆ (dyadicBlock N).powersetCard 2 :=
    fun e he ↦ (mem_filter.mp (mem_sdiff.mp he).1).1
  obtain ⟨hweakact, hexact⟩ := hpart N (by omega) L hband
  have hweak : classMass (dyadicBlock N) L u (weak Q N H L) ≤ P := by
    calc
      _ ≤ (N : ℝ) ^ (-1 / 2 + δ) * CompatibleActivitySplit.absolute L (weak Q N H L) :=
        hi N (by omega) L hband (dyadicBlock N) Subset.rfl _ hweaksub
      _ ≤ (N : ℝ) ^ (-1 / 2 + δ) * (N : ℝ) ^ (-1 + δ + δ) :=
        mul_le_mul_of_nonneg_left hweakact (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ ((-1 / 2 + δ) + (-1 + δ + δ)) := (Real.rpow_add hn _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε])
  have hex : classMass (dyadicBlock N) L u (exceptional Q N H L) ≤ P := by
    calc
      _ ≤ (N : ℝ) ^ (-1 / 2 + δ) * CompatibleActivitySplit.absolute L (exceptional Q N H L) :=
        hi N (by omega) L hband (dyadicBlock N) Subset.rfl _ hexsub
      _ ≤ (N : ℝ) ^ (-1 / 2 + δ) * (N : ℝ) ^ (-1 + δ) :=
        mul_le_mul_of_nonneg_left hexact (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ ((-1 / 2 + δ) + (-1 + δ)) := (Real.rpow_add hn _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε])
  have hpower : (N : ℝ) ^ (-3 / 2 + δ) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hε])
  have hsmall : (∑ k ∈ Ico 1 s, u ^ k * FixedPairExtensions.deficit (dyadicBlock N) L k) ≤ K * P :=
    (hf N (by omega) L hband (dyadicBlock N) Subset.rfl).trans
      (mul_le_mul_of_nonneg_left hpower hK)
  have hlarge : (∑ e ∈ good Q N H L, |infiniteCenteredCoefficient L e| *
      ∑ A ∈ largeSeeds (dyadicBlock N) L e s, ∏ x ∈ A, u * infiniteMarginal x L) ≤ P :=
    (ht N (by omega) L hband).trans hpower
  have hmean : (∑ x ∈ dyadicBlock N, u * infiniteMarginal x L) ≤ u * M := by
    rw [← mul_sum]
    apply mul_le_mul_of_nonneg_left _ hu.le
    have h := (hm N (by omega) L hband).2
    rw [CountObservables.countMoment_one Subset.rfl] at h
    exact h
  have hgood : classMass (dyadicBlock N) L u (good Q N H L) ≤ Real.exp (u * M) * (K + 1) * P := by
    have hseed := class_seed_bound (dyadicBlock N) L u hu.le s (good Q N H L) hgoodsub
    have hsum : (∑ k ∈ Ico 1 s, u ^ k * FixedPairExtensions.deficit (dyadicBlock N) L k) +
        (∑ e ∈ good Q N H L, |infiniteCenteredCoefficient L e| *
          ∑ A ∈ largeSeeds (dyadicBlock N) L e s, ∏ x ∈ A, u * infiniteMarginal x L) ≤ (K + 1) * P := by
      linarith only [hsmall, hlarge]
    calc
      _ ≤ Real.exp (∑ x ∈ dyadicBlock N, u * infiniteMarginal x L) * ((K + 1) * P) :=
        hseed.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _))
      _ ≤ Real.exp (u * M) * ((K + 1) * P) := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr hmean) (mul_nonneg (by linarith only [hK]) hP)
      _ = _ := by ring
  calc
    _ = classMass (dyadicBlock N) L u (good Q N H L) + classMass (dyadicBlock N) L u (weak Q N H L) +
        classMass (dyadicBlock N) L u (exceptional Q N H L) := partition Q N H L hL u
    _ ≤ A * P := by dsimp [A]; linarith only [hgood, hweak, hex]
    _ ≤ (N : ℝ) ^ ((-3 / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.AllPairDeficit
