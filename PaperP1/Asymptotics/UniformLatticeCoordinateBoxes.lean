module

public import PaperP1.Asymptotics.UniformReducedBinaryBasis
public import PaperP1.Analysis.ReducedLatticeCoordinateBoxes

/-! # Actual reduced coordinate boxes with uniform heights and determinant-controlled area -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformLatticeCoordinateBoxes

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds
open PaperP1.ReducedLatticeCoordinateBoxes

theorem uniform_coordinate_boxes (μ : ℕ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ T S : Matrix (Fin 2) (Fin 2) ℝ, S * T = 1 →
      (∀ i j, |T i j| ≤ ((N ^ μ : ℕ) : ℝ)) → (∀ i j, |S i j| ≤ ((N ^ μ : ℕ) : ℝ)) →
      ∀ R : ℝ, 0 ≤ R →
      ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ,
        L₀ = sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ∧
        L₁ = sideLength R (squareNorm (realImage T (fun i ↦ A i 1))) ∧
        A * B = 1 ∧ B * A = 1 ∧ A.det = 1 ∧
        (∀ i j, |A i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧ (∀ i j, |B i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        (∀ w : Fin 2 → ℤ, w ≠ 0 →
          squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) ∧
        0 ≤ L₁ ∧ L₁ ≤ L₀ ∧ L₀ * L₁ ≤ 4 * R ^ 2 / |T.det| ∧
        L₀ ≤ 2 * R * (((2 * (N ^ μ) ^ 2 : ℕ) : ℝ) + 1) ∧
        R ^ 2 ≤ L₀ ^ 2 * |T.det| ∧
        ∀ z : Fin 2 → ℤ, (∀ i, |realImage T z i| ≤ R) →
          |(B.mulVec z 0 : ℝ)| ≤ L₀ ∧ |(B.mulVec z 1 : ℝ)| ≤ L₁ := by
  obtain ⟨κ, N₀, hbasis⟩ := UniformReducedBinaryBasis.uniform_reduced_basis μ
  refine ⟨κ, N₀, ?_⟩
  intro N hN T S hST hT hS R hR
  obtain ⟨A, B, hAB, hBA, hdet, hA, hB, hmin, hp, horder, _, harea⟩ := hbasis N hN T S hST hT hS
  have hc := actual_side_controls T S hST A B hBA hdet R hR hp horder harea
  refine ⟨A, B, sideLength R (squareNorm (realImage T (fun i ↦ A i 0))),
    sideLength R (squareNorm (realImage T (fun i ↦ A i 1))), rfl, rfl, hAB, hBA, hdet, hA, hB, hmin,
    ?_, hc.1, hc.2.1, ?_, hc.2.2.2, ?_⟩
  · unfold sideLength
    positivity
  · exact hc.2.2.1.trans (by
      gcongr
      exact BinaryLatticeEntryBounds.inverseSize_bound S (N ^ μ) hS)
  · intro z hz
    exact actual_coordinate_bounds T A B hAB hdet R hR hp horder harea z hz

end PaperP1.UniformLatticeCoordinateBoxes
