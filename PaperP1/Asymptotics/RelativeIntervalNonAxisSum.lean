module

public import PaperP1.Asymptotics.RelativeIntervalNonAxisCount
public import PaperP1.Analysis.FiniteSquareTail

/-! # The actual non-axis first-lattice side sum has square-root source scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalNonAxisSum

open Finset PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals
open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds

theorem uniform_nonaxis_sum (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 1 ≤ M → M ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E → ∀ I : Finset ℕ, I ⊆ intervalIndices M →
      ∀ z : ℕ → Fin 2 → ℤ,
      (∀ k ∈ I, z k 0 ≠ 0 ∧ z k 1 ≠ 0 ∧ (z k 1).natAbs ≤ N ^ κ) →
      let L := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
      (∑ k ∈ I, L k) ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (D * E * M) := by
  obtain ⟨N₀, hcount⟩ := RelativeIntervalNonAxisCount.uniform_nonaxis_intervals κ (2 * ε) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN D E hD hE I hI z hz
  let f := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
  let C := 432 * (N : ℝ) ^ (2 * ε) * (D * E)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : ∀ k ∈ I, 0 ≤ f k := by intro k _; dsimp [f, sideLength]; positivity
  have htail : ∀ t : ℝ, 0 < t → ((I.filter (fun k ↦ t ≤ f k)).card : ℝ) ≤ C / t ^ 2 := by
    intro t ht
    apply hcount N hN M hM hMN D E t hD hE ht (I.filter (fun k ↦ t ≤ f k))
      (fun k hk ↦ hI (mem_filter.mp hk).1) z
    · intro k hk
      exact hz k (mem_filter.mp hk).1
    · intro k hk
      exact (mem_filter.mp hk).2
  have hsum := FiniteSquareTail.sum_bound_of_div_tail I f C hC hf htail
  have hcard : (I.card : ℝ) ≤ 2 * M := by
    exact_mod_cast (show I.card ≤ 2 * M from (card_le_card hI).trans_eq (intervalIndices_card M))
  have hpow : (N : ℝ) ^ (2 * ε) = ((N : ℝ) ^ ε) ^ 2 := by
    simpa only [Nat.cast_ofNat, mul_comm] using Real.rpow_mul_natCast (Nat.cast_nonneg N) ε 2
  have hbase := mul_le_mul_of_nonneg_left hcard hC
  have hsize : 2 * Real.sqrt C * Real.sqrt I.card ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (D * E * M) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt (Nat.cast_nonneg I.card),
      Real.sq_sqrt (show 0 ≤ D * E * (M : ℝ) by positivity)]
    dsimp [C] at hbase ⊢
    rw [hpow] at hbase ⊢
    have hnonnegative : 0 ≤ ((N : ℝ) ^ ε) ^ 2 * (D * E * M) := by positivity
    nlinarith
  exact hsum.trans hsize

end PaperP1.RelativeIntervalNonAxisSum
