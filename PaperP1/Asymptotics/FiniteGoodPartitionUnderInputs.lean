module

public import PaperP1.Model.FiniteGoodChannelPartition
public import PaperP1.Asymptotics.FiniteChannelActivityBounds
public import PaperP1.Asymptotics.NonalignedPairActivityUnderInputs
public import PaperP1.Asymptotics.BoundaryAlignedActivity
public import PaperP1.Asymptotics.LogHeightAlignedActivity
public import PaperP1.Asymptotics.IncompatiblePairActivity

/-! # The actual finite-channel partition under explicit geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGoodPartitionUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteGoodChannelPartition
  PaperP1.FiniteAlignedChannelCover

theorem choose_height (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, 3 ≤ Q ∧ 1 / ((Q + 1 : ℕ) : ℝ) ≤ η / 2 := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < η / 2 by positivity)
  refine ⟨max 3 n, le_max_left _ _, ?_⟩
  have hmono : (n : ℝ) + 1 ≤ ((max 3 n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ max 3 n + 1 by omega)
  exact (one_div_le_one_div_of_le (by positivity) hmono).trans hn.le

theorem uniform_exceptional (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 64)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        CompatibleActivitySplit.absolute L (exceptional Q N (2 * Q * (L + 1)) L) ≤
          (N : ℝ) ^ (-1 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hnon⟩ := NonalignedPairActivityUnderInputs.uniform_activity C (ε / 2) (by positivity)
  rw [show ((ε / 2) / 2) / 16 = ε / 64 by ring] at hnon
  obtain ⟨N1, _hN1, h1⟩ := BoundaryAlignedActivity.height_one C (ε / 2) (by positivity)
  obtain ⟨N2, _hN2, h2⟩ := BoundaryAlignedActivity.height_two C (ε / 2) (by positivity)
  obtain ⟨NZ, _hNZ, hz⟩ := ZeroUnitAlignedActivity.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨ND, _hND, hd⟩ := FiniteChannelActivityBounds.uniform_bounds Q C (ε / 2) (by positivity)
  obtain ⟨NI, _hNI, hi⟩ := IncompatiblePairActivityAsymptotic.uniform_activity C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (Q + 2)
  obtain ⟨NL, hl⟩ := CriticalPolynomialScale.polynomial_lt_scale C 2 (by norm_num) 4
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 6 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NN, _hNN, hn⟩ := hnon hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NN (max N1 (max N2 (max NZ (max ND (max NI (max NG (max NL NF)))))))), by omega, ?_⟩
  intro N hN L hband
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 0 < L := by omega
  have hheight : Q ≤ (L + 1) ^ 3 := (show Q ≤ L + 1 by omega).trans
    (le_self_pow₀ (by omega : 1 ≤ L + 1) (by decide : 3 ≠ 0))
  have hlarge : 2 * (L + 1) ^ 4 < N := by exact_mod_cast hl N (by omega) L hband
  have hfinite := exceptional_activity_bound (H := 2 * Q * (L + 1)) (by omega : 2 ≤ N) hL hheight hlarge
  have h0 := hn N (by omega) L hband
  have h1 := h1 N (by omega) L hband
  have h2 := (h2 N (by omega) L hband).2
  have h3 := hz N (by omega) L hband
  have h4 := (hd N (by omega) L hband).2.1
  have h5 : CompatibleActivitySplit.absolute L (incompatible N L) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    hi N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hclasses : (∑ i ∈ range 6, CompatibleActivitySplit.absolute L
      (exceptionalClasses Q N (2 * Q * (L + 1)) L i)) =
      CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) +
      CompatibleActivitySplit.absolute L (BoundaryAlignedPairs.channel N L 1 1) +
      CompatibleActivitySplit.absolute L (BoundaryAlignedPairs.channel N L 1 2) +
      CompatibleActivitySplit.absolute L (AlignedChannelFamilies.zeroFamilies N L) +
      CompatibleActivitySplit.absolute L (defectivePairs Q N (2 * Q * (L + 1)) L) +
      CompatibleActivitySplit.absolute L (incompatible N L) := by
    simp [sum_range_succ, exceptionalClasses]
  rw [hclasses] at hfinite
  calc
    _ ≤ 6 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hfinite, h0, h1, h2, h3, h4, h5]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T7_1 (η : ℝ) (hη : 0 < η) :
    ∃ Q : ℕ, 3 ≤ Q ∧ ∀ C ε : ℝ, 0 < ε →
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (ε / 128)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (CompatibleActivitySplit.absolute L (weak Q N (2 * Q * (L + 1)) L) ≤
          (N : ℝ) ^ (-1 + η + ε) ∧
        CompatibleActivitySplit.absolute L (exceptional Q N (2 * Q * (L + 1)) L) ≤
          (N : ℝ) ^ (-1 + ε) ∧
        (∀ G : Finset ℕ, G ⊆ dyadicBlock N → HeterogeneousRunConversion.absoluteMass G L ≤
          (N : ℝ) ^ (-2 / 3 + ε)) ∧
        ∀ e ∈ good Q N (2 * Q * (L + 1)) L, ∃ ab ∈ channels Q,
          e ∈ PrivateChannelActivity.pairs N (2 * Q * (L + 1)) ab.1 ab.2 L ∧
          |infiniteCenteredCoefficient L e| ≤ (N : ℝ) ^ (-2 + 1 / (ab.2 : ℝ) + ε) ∧
          ∃ x y : ℕ, e = {x, y} ∧ GoodEdgeCompression.Conclusion ab.1 ab.2 x y L)) := by
  obtain ⟨Q, hQ, hηQ⟩ := choose_height η hη
  refine ⟨Q, hQ, ?_⟩
  intro C ε hε
  obtain ⟨Ds, k, k₁, k₂, hDs, hexception⟩ := uniform_exceptional Q C (ε / 2) (by positivity)
  rw [show (ε / 2) / 64 = ε / 128 by ring] at hexception
  obtain ⟨NP, _hNP, hp⟩ := FiniteChannelActivityBounds.uniform_bounds Q C (ε / 2) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := LogHeightAlignedActivity.uniform_bound (Q + 1) (by omega) C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨NE, _hNE, he⟩ := hexception hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨max 2 (max NE (max NP (max NW (max NG NF)))), by omega, ?_⟩
  intro N hN L hband
  classical
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hprivate := hp N (by omega) L hband
  have hex := he N (by omega) L hband
  have hweak : CompatibleActivitySplit.absolute L (weak Q N (2 * Q * (L + 1)) L) ≤
      (N : ℝ) ^ (-1 + 1 / ((Q + 1 : ℕ) : ℝ) + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans inter_subset_right)
      (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans
      (hw N (by omega) L hband)
  have hinv : 1 / ((Q + 1 : ℕ) : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 4 ≤ Q + 1 by omega))
  have hwsharp : CompatibleActivitySplit.absolute L (weak Q N (2 * Q * (L + 1)) L) ≤
      (N : ℝ) ^ (-2 / 3 + ε / 2) := hweak.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hinv]))
  have hesharp : CompatibleActivitySplit.absolute L (exceptional Q N (2 * Q * (L + 1)) L) ≤
      (N : ℝ) ^ (-2 / 3 + ε / 2) := hex.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num; linarith))
  have hgsharp : CompatibleActivitySplit.absolute L (good Q N (2 * Q * (L + 1)) L) ≤
      (N : ℝ) ^ (-2 / 3 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg (fun e hgood ↦ (mem_filter.mp hgood).2.2)
      (fun e _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L e))).trans hprivate.1
  have hdecomp := activity_decomposition Q N (2 * Q * (L + 1)) L hL
  have hall : HeterogeneousRunConversion.absoluteMass (dyadicBlock N) L ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
    calc
      _ ≤ 3 * (N : ℝ) ^ (-2 / 3 + ε / 2) := by
        change CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) ≤ _
        linarith only [hdecomp, hwsharp, hesharp, hgsharp]
      _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
      _ = _ := by congr 1; ring
  refine ⟨hweak.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hηQ, hη, hε])),
    hex.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])),
    fun G hG ↦ (PairActivityHostCap.absoluteMass_mono hG L).trans hall, ?_⟩
  intro e hgood
  obtain ⟨ab, hab, heab, x, y, heq, hcomp⟩ := good_compression (by omega : 2 ≤ N) hgood
  refine ⟨ab, hab, heab, ?_, x, y, heq, hcomp⟩
  exact (hprivate.2.2 ab hab e heab).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε]))

end PaperP1.FiniteGoodPartitionUnderInputs
