module

public import PaperP1.Asymptotics.UniformVerticalGridCoordinates

/-! # Literal coordinate data for a consistently chosen actual vertical grid basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VerticalGridCoordinateData

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
open PaperP1.EffectiveSourceCoordinates PaperP1.BinaryLatticeMinimum
open PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds PaperP1.VerticalGridMatrices

structure Data {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (κ M q : ℕ)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (L₀ L₁ : ℝ) : Prop where
  large_eq : L₀ = sideLength (2 * (49 + 16 / ρ))
    (squareNorm (realImage (gridTransform X M q) (fun i ↦ A i 0)))
  small_eq : L₁ = sideLength (2 * (49 + 16 / ρ))
    (squareNorm (realImage (gridTransform X M q) (fun i ↦ A i 1)))
  right_inverse : A * B = 1
  left_inverse : B * A = 1
  determinant : A.det = 1
  basis_height : ∀ i j, |A i j| ≤ ((N ^ κ : ℕ) : ℤ)
  inverse_height : ∀ i j, |B i j| ≤ ((N ^ κ : ℕ) : ℤ)
  first_shortest : ∀ w : Fin 2 → ℤ, w ≠ 0 →
    squareNorm (realImage (gridTransform X M q) (fun i ↦ A i 0)) ≤
      squareNorm (realImage (gridTransform X M q) w)
  small_nonnegative : 0 ≤ L₁
  side_order : L₁ ≤ L₀
  side_product : L₀ * L₁ ≤ 4 * (2 * (49 + 16 / ρ)) ^ 2 * C ^ 2 * (X.U * X.V) / (ρ ^ 2 * M)
  large_upper : L₀ ≤ 2 * (2 * (49 + 16 / ρ)) * (((2 * (N ^ 2) ^ 2 : ℕ) : ℝ) + 1)
  large_lower : (2 * (49 + 16 / ρ)) ^ 2 * C ^ 2 * (scale N X.c₁ X.D * scale N X.c₂ X.E) / M ≤ L₀ ^ 2
  points : ∀ h : ℤ, (M : ℝ) * |(h : ℝ)| ≤ N → ∀ S : Finset Quad, SignedPopulation X h S →
    ∀ p ∈ S, QuadraticIntervalGrid.grid M (intervalIndex M X.D X.E p.1.1 p.1.2) = q →
    |(B.mulVec ![(p.2.2 : ℤ), (p.2.1 : ℤ)] 0 : ℝ)| ≤ L₀ ∧
      |(B.mulVec ![(p.2.2 : ℤ), (p.2.1 : ℤ)] 1 : ℝ)| ≤ L₁

theorem uniform_data (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ, ∀ q : ℕ, q ≤ 4 * M →
        ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ, Data X κ M q A B L₀ L₁ := by
  obtain ⟨κ, N₀, hcoords⟩ := UniformVerticalGridCoordinates.uniform_vertical_coordinates C ρ hC hρ
  refine ⟨κ, N₀, ?_⟩
  intro N hN M hM hMN δ X q hq
  obtain ⟨A, B, L₀, L₁, hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct, hupper, hlower, hpoints⟩ := hcoords N hN M hM hMN δ X q hq
  exact ⟨A, B, L₀, L₁, ⟨hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct, hupper, hlower, hpoints⟩⟩

end PaperP1.VerticalGridCoordinateData
