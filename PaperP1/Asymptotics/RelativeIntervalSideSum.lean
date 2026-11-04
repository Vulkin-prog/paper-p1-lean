module

public import PaperP1.Asymptotics.RelativeIntervalNonAxisSum

/-! # Complete actual first-lattice side summation, including both primitive axes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalSideSum

open Finset PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals
open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds

theorem three_filter_cover (I : Finset ℕ) (z : ℕ → Fin 2 → ℤ) (f : ℕ → ℝ)
    (hf : ∀ k ∈ I, 0 ≤ f k) :
    (∑ k ∈ I, f k) ≤ (∑ k ∈ I.filter (fun k ↦ z k 0 = 0), f k) +
      (∑ k ∈ I.filter (fun k ↦ z k 1 = 0), f k) +
      (∑ k ∈ I.filter (fun k ↦ z k 0 ≠ 0 ∧ z k 1 ≠ 0), f k) := by
  simp only [sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro k hk
  by_cases h0 : z k 0 = 0 <;> by_cases h1 : z k 1 = 0 <;> simp [h0, h1]; linarith [hf k hk]

theorem uniform_first_lattice_sum (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 1 ≤ M → M ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E → ∀ I : Finset ℕ, I ⊆ intervalIndices M →
      (∀ k ∈ I, (M : ℝ) / 4 ≤ k) → ∀ z : ℕ → Fin 2 → ℤ,
      (∀ k ∈ I, (z k 0).natAbs.Coprime (z k 1).natAbs) →
      (∀ k ∈ I, (z k 1).natAbs ≤ N ^ κ) →
      let L := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
      (∑ k ∈ I, L k) ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (D * E * M) + 32 * E + 8 * D := by
  obtain ⟨N₀, hnonaxis⟩ := RelativeIntervalNonAxisSum.uniform_nonaxis_sum κ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN D E hD hE I hI hklow z hprimitive hheight
  let f := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
  have hf : ∀ k ∈ I, 0 ≤ f k := by intro k _; dsimp [f, sideLength]; positivity
  have hcover := three_filter_cover I z f hf
  have haxes := RelativeIntervalAxisBounds.actual_axis_sums M hM I hI hklow D E hD hE z hprimitive
  have hother := hnonaxis N hN M hM hMN D E hD hE
    (I.filter (fun k ↦ z k 0 ≠ 0 ∧ z k 1 ≠ 0)) (fun k hk ↦ hI (mem_filter.mp hk).1) z
    (fun k hk ↦ ⟨(mem_filter.mp hk).2.1, (mem_filter.mp hk).2.2, hheight k (mem_filter.mp hk).1⟩)
  change (∑ k ∈ I, f k) ≤ _
  change (∑ k ∈ I.filter (fun k ↦ z k 0 = 0), f k) ≤ _ ∧
    (∑ k ∈ I.filter (fun k ↦ z k 1 = 0), f k) ≤ _ at haxes
  change (∑ k ∈ I.filter (fun k ↦ z k 0 ≠ 0 ∧ z k 1 ≠ 0), f k) ≤ _ at hother
  linarith [haxes.1, haxes.2]

end PaperP1.RelativeIntervalSideSum
