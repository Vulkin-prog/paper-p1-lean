module

public import PaperP1.Arithmetic.SourcePairKernelComparison
public import PaperP1.Asymptotics.DenseWeightedSectorUnderInputs

/-! # The dense arithmetic source rank, including every local kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseSourcePairKernelUnderInputs

open Finset PaperP1.LargePrimeGraphResolution

theorem uniform_source_kernel (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap η) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
        (∑ p ∈ F, ((2 ^ NormalizedPairRankLoss.pairLoss p.1 p.2 L : ℝ) - 1)) ≤ A * (N : ℝ) ^ (1 + ε)) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hbound⟩ := DenseWeightedSectorUnderInputs.uniform_full_weight C ε η hε hη
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, N₀, hcount⟩ := hbound hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L hcrit F hdyadic hnon hdensity
  exact (SourcePairKernelComparison.source_kernel_le_full_sum F L).trans
    (hcount N hN L hcrit F hdyadic hnon hdensity)

end PaperP1.DenseSourcePairKernelUnderInputs
