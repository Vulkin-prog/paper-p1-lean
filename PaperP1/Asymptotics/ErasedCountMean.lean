module

public import PaperP1.Model.ErasedCountReference
public import PaperP1.Asymptotics.OriginalDeletedIntensity

/-! # The actual erased mean and its exact independent-background intensity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ErasedCountMean

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ErasedCountReference
  PaperP1.AllPairCountMeans PaperP1.PositionalFactorialCovariance PaperP1.PositionalDeletedFields

theorem uniform_positive (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ, 0 < singleMean H N L := by
  obtain ⟨NP, hNP, hp⟩ := WeakPairIncidence.full_single_rates_positive C
  refine ⟨NP, hNP, ?_⟩
  intro N hN L hband H
  rw [singleMean_eq_sum (by omega : 2 ≤ N) H]
  apply sum_pos (fun x _hx ↦ hp N hN L hband H x)
  exact ⟨N, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩

theorem uniform_error (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
        |goodMean H N L - singleMean H N L| ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := OriginalDeletedIntensity.uniform_bound C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband H
  have hh := h N hN L hband H
  have hfirst : 0 ≤ ∑ x ∈ dyadicBlock N, |mean
      (onceLaw (GoodEdgeCompression.goodEdges H N L) (dyadicBlock N) L) x -
        ((2 ^ L : ℝ)⁻¹ - PositionalCompoundPoisson.incidence
          (GoodEdgeCompression.goodEdges H N L) (infiniteJointMoment L) x)| :=
    sum_nonneg (fun _ _ ↦ abs_nonneg _)
  rw [goodMean_eq_sum, singleMean_eq_sum (by omega : 2 ≤ N) H, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  linarith only [hh, hfirst]

end PaperP1.ErasedCountMean
