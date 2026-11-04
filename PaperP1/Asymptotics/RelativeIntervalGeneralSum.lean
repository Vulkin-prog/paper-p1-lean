module

public import PaperP1.Asymptotics.RelativeIntervalSideSum
public import PaperP1.Analysis.RelativeIntervalGeneralAxis

/-! # Actual side summation with any fixed positive lower index proportion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalGeneralSum

open Finset PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals
open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds

theorem uniform_lattice_sum (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 1 ≤ M → M ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E → ∀ I : Finset ℕ, I ⊆ intervalIndices M →
      ∀ A : ℝ, 0 ≤ A → (∀ k ∈ I, (M : ℝ) ≤ A * k) → ∀ z : ℕ → Fin 2 → ℤ,
      (∀ k ∈ I, (z k 0).natAbs.Coprime (z k 1).natAbs) →
      (∀ k ∈ I, (z k 1).natAbs ≤ N ^ κ) →
      let L := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
      (∑ k ∈ I, L k) ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (D * E * M) + 8 * A * E + 8 * D := by
  obtain ⟨N₀, hnonaxis⟩ := RelativeIntervalNonAxisSum.uniform_nonaxis_sum κ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN D E hD hE I hI A hA hklow z hprimitive hheight
  let f := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
  have hf : ∀ k ∈ I, 0 ≤ f k := by intro k _; dsimp [f, sideLength]; positivity
  have hcover := RelativeIntervalSideSum.three_filter_cover I z f hf
  have haxes := RelativeIntervalGeneralAxis.actual_axis_sums M hM I hI A hA hklow D E hD hE z hprimitive
  have hother := hnonaxis N hN M hM hMN D E hD hE
    (I.filter (fun k ↦ z k 0 ≠ 0 ∧ z k 1 ≠ 0)) (fun k hk ↦ hI (mem_filter.mp hk).1) z
    (fun k hk ↦ ⟨(mem_filter.mp hk).2.1, (mem_filter.mp hk).2.2, hheight k (mem_filter.mp hk).1⟩)
  change (∑ k ∈ I, f k) ≤ _
  change (∑ k ∈ I.filter (fun k ↦ z k 0 = 0), f k) ≤ _ ∧
    (∑ k ∈ I.filter (fun k ↦ z k 1 = 0), f k) ≤ _ at haxes
  change (∑ k ∈ I.filter (fun k ↦ z k 0 ≠ 0 ∧ z k 1 ≠ 0), f k) ≤ _ at hother
  linarith [haxes.1, haxes.2]

end PaperP1.RelativeIntervalGeneralSum
