module

public import PaperP1.Asymptotics.QuadraticLatticeSideSum

/-! # The quadratic-grid side sum retains the actual fixed image radius -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticGridRadiusSum

open Finset PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals
open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds
open PaperP1.QuadraticIntervalGrid

theorem side_length_scaling (R P : ℝ) : sideLength R P = (R / 2) * sideLength 2 P := by
  unfold sideLength
  ring

theorem uniform_radius_sum (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E → ∀ I : Finset ℕ,
      (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) → ∀ z : ℕ → Fin 2 → ℤ,
      (∀ q ∈ I.image (grid M), (z q 0).natAbs.Coprime (z q 1).natAbs) →
      (∀ q ∈ I.image (grid M), (z q 1).natAbs ≤ N ^ κ) → ∀ R : ℝ, 0 ≤ R →
      let L := fun q ↦ sideLength R (squareNorm (realImage
        (transform D E (2 * M) (intervalCenter (2 * M) D E q)) (z q)))
      (∑ k ∈ I, L (grid M k)) ≤
        (R / 2) * (120 * (N : ℝ) ^ ε * Real.sqrt (D * E * (2 * M)) + 1024 * E + 16 * D) := by
  obtain ⟨N₀, hsum⟩ := QuadraticLatticeSideSum.uniform_grid_sum κ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN D E hD hE I hlow hupper z hprimitive hheight R hR
  have hb := hsum N hN M hM hMN D E hD hE I hlow hupper z hprimitive hheight
  have hscaled := mul_le_mul_of_nonneg_left hb (show 0 ≤ R / 2 by positivity)
  change (∑ k ∈ I, sideLength R _) ≤ _
  simpa only [side_length_scaling R, Finset.mul_sum] using hscaled

end PaperP1.QuadraticGridRadiusSum
