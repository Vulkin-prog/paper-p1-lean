module

public import PaperP1.Model.SourcePairActivityBound
public import PaperP1.Asymptotics.NonalignedSourceResidualUnderInputs
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # The full actual nonaligned pair activity has conditional exponent -1+epsilon

The full arithmetic pair loss retains local kernels. No regularity or affine
compatibility restriction is imposed on the actual pair population.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedPairActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NonalignedActivityHostCap

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap ((ε / 2) / 16)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        CompatibleActivitySplit.absolute L (AllAlignedPairs.nonaligned N L) ≤
          (N : ℝ) ^ (-1 + ε)) := by
  classical
  obtain ⟨Ds, k, k₁, k₂, hDs, hw⟩ := NonalignedSourceResidualUnderInputs.uniform_weighted_hosts
    C (ε / 2) (by positivity)
  obtain ⟨NI, hi⟩ := PairHostIndependentMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, NW, hw⟩ := hw hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  let K := 2 * ((2 : ℝ) ^ C) ^ 2 * A
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (K + 1) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NI (max NG (max NW NF))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hweights := hw N (by omega) L hband (sources N L)
    (fun p hp ↦ mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1)
    (fun _ hp ↦ (mem_filter.mp hp).2.2)
  have hsum0 : 0 ≤ ∑ p ∈ sources N L, SourcePairPositiveWeight.weight p.1 p.2 L :=
    sum_nonneg fun p _ ↦ SourcePairPositiveWeight.weight_nonneg p.1 p.2 L
  have hnominal := CriticalChannelPowers.nominal_square_upper (by omega : 2 ≤ N) hband
  have hjoint : (2 * ((2 ^ L : ℝ)⁻¹) ^ 2) *
      (∑ p ∈ sources N L, SourcePairPositiveWeight.weight p.1 p.2 L) ≤
        K * (N : ℝ) ^ (-1 + ε / 2) := by
    calc
      _ ≤ (2 * (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ))) *
          (A * (N : ℝ) ^ (1 + ε / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnominal (by norm_num)) hweights hsum0 (by positivity)
      _ = K * (N : ℝ) ^ (-1 + ε / 2) := by
        dsimp [K]
        rw [show -1 + ε / 2 = (-2 : ℝ) + (1 + ε / 2) by ring, Real.rpow_add hn (-2) (1 + ε / 2)]
        ring
  have hfinite := SourcePairActivityBound.weighted_bound (N := N) (by omega) hL
  have hind := hi N (by omega) L hband
  calc
    _ ≤ (K + 1) * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hfinite, hjoint, hind]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.NonalignedPairActivityUnderInputs
