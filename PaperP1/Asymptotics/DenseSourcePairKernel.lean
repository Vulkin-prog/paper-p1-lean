module

public import PaperP1.Asymptotics.DenseWeightedSector
public import PaperP1.Arithmetic.SourcePairKernelComparison

/-! # The actual dense source kernel bound follows from the full value-kernel sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseSourcePairKernel

open Finset PaperP1.Model PaperP1.LargePrimeGraphResolution

theorem uniform_source_kernel (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
      (∑ p ∈ F, ((2 ^ NormalizedPairRankLoss.pairLoss p.1 p.2 L : ℝ) - 1)) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := DenseWeightedSector.uniform_full_weight C ε η hε hη
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  exact (SourcePairKernelComparison.source_kernel_le_full_sum F L).trans
    (h N hN L hband F hdyadic hnon hdense)

end PaperP1.DenseSourcePairKernel
