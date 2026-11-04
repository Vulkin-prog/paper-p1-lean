module

public import PaperP1.Asymptotics.RelativeIntervalGeneralSum
public import PaperP1.Arithmetic.QuadraticGridWeights

/-! # Actual second-grid side summation pulled back to the original interval indices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticLatticeSideSum

open Finset PaperP1.RelativeIntervalLattice PaperP1.DeterminantRelativeIntervals
open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds
open PaperP1.QuadraticIntervalGrid

theorem uniform_grid_sum (κ : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ D E : ℝ, 0 < D → 0 < E → ∀ I : Finset ℕ,
      (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) → ∀ z : ℕ → Fin 2 → ℤ,
      (∀ q ∈ I.image (grid M), (z q 0).natAbs.Coprime (z q 1).natAbs) →
      (∀ q ∈ I.image (grid M), (z q 1).natAbs ≤ N ^ κ) →
      let L := fun q ↦ sideLength 2 (squareNorm (realImage
        (transform D E (2 * M) (intervalCenter (2 * M) D E q)) (z q)))
      (∑ k ∈ I, L (grid M k)) ≤
        120 * (N : ℝ) ^ ε * Real.sqrt (D * E * (2 * M)) + 1024 * E + 16 * D := by
  obtain ⟨N₀, hsum⟩ := RelativeIntervalGeneralSum.uniform_lattice_sum κ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN M hM hMN D E hD hE I hlow hupper z hprimitive hheight
  let J := I.image (grid M)
  have hJ : J ⊆ intervalIndices (2 * M) := by
    simpa only [intervalIndices, show 2 * (2 * M) = 4 * M by omega] using
      QuadraticGridWeights.image_subset M hM I hlow hupper
  have hJlow : ∀ q ∈ J, ((2 * M : ℕ) : ℝ) ≤ 64 * q := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
    have hb : (M : ℝ) ≤ 32 * (grid M k : ℝ) := by exact_mod_cast grid_lower M k hM (hlow k hk)
    push_cast
    linarith
  let f := fun q ↦ sideLength 2 (squareNorm (realImage
    (transform D E (2 * M) (intervalCenter (2 * M) D E q)) (z q)))
  have hgrid := hsum N hN (2 * M) (by omega) hMN D E hD hE J hJ 64 (by norm_num) hJlow z hprimitive hheight
  have hf : ∀ q ∈ J, 0 ≤ f q := by intro q _; dsimp [f, sideLength]; positivity
  have htransfer := QuadraticGridWeights.weighted_sum_bound M (by omega) I hlow f hf
  push_cast at hgrid
  change (∑ q ∈ J, f q) ≤ _ at hgrid
  change (∑ k ∈ I, f (grid M k)) ≤ _
  have hm := mul_le_mul_of_nonneg_left hgrid (show (0 : ℝ) ≤ 2 by norm_num)
  linarith

end PaperP1.QuadraticLatticeSideSum
