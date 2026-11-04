module

public import PaperP1.Asymptotics.UniformRelativeIntervalCoordinates
public import PaperP1.Arithmetic.DeterminantSourceBox

/-! # Actual horizontal coordinate data for every original source interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HorizontalGridCoordinateData

open PaperP1.DeterminantSourceBox PaperP1.RelativeIntervalLattice
open PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum
open PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds

structure Data {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (κ M k : ℕ)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (L₀ L₁ : ℝ) : Prop where
  large_eq : L₀ = sideLength 2 (squareNorm (realImage
    (transform X.D X.E M (intervalCenter M X.D X.E k)) (fun i ↦ A i 0)))
  small_eq : L₁ = sideLength 2 (squareNorm (realImage
    (transform X.D X.E M (intervalCenter M X.D X.E k)) (fun i ↦ A i 1)))
  right_inverse : A * B = 1
  left_inverse : B * A = 1
  determinant : A.det = 1
  basis_height : ∀ i j, |A i j| ≤ ((N ^ κ : ℕ) : ℤ)
  inverse_height : ∀ i j, |B i j| ≤ ((N ^ κ : ℕ) : ℤ)
  first_shortest : ∀ w : Fin 2 → ℤ, w ≠ 0 →
    squareNorm (realImage (transform X.D X.E M (intervalCenter M X.D X.E k)) (fun i ↦ A i 0)) ≤
      squareNorm (realImage (transform X.D X.E M (intervalCenter M X.D X.E k)) w)
  small_nonnegative : 0 ≤ L₁
  side_order : L₁ ≤ L₀
  side_product : L₀ * L₁ ≤ 16 * (X.D * X.E) / M
  large_upper : L₀ ≤ 4 * (((2 * (N ^ 2) ^ 2 : ℕ) : ℝ) + 1)
  large_lower : 4 * (X.D * X.E) / M ≤ L₀ ^ 2
  points : ∀ z : Fin 2 → ℤ, X.D ≤ (z 0 : ℝ) → (z 0 : ℝ) ≤ 2 * X.D →
    X.E ≤ (z 1 : ℝ) → (z 1 : ℝ) ≤ 2 * X.E →
    intervalIndex M X.D X.E (z 0 : ℝ) (z 1 : ℝ) = k →
    |(B.mulVec z 0 : ℝ)| ≤ L₀ ∧ |(B.mulVec z 1 : ℝ)| ≤ L₁

theorem uniform_data (C : ℝ) (_hC : 0 < C) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 4 ≤ M → M ≤ N →
      ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ k : ℕ, k ≤ 2 * M →
        ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ, Data X κ M k A B L₀ L₁ := by
  let Q := ⌈C⌉₊ + 1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hQR : C ≤ (Q : ℝ) := by
    have hh := Nat.le_ceil C
    dsimp [Q]
    push_cast
    linarith
  obtain ⟨κ, N₀, hcoords⟩ := UniformRelativeIntervalCoordinates.uniform_interval_coordinates Q hQ
  refine ⟨κ, N₀, ?_⟩
  intro N hN M hM hMN ρ δ X k hk
  have hDN := (DeterminantBoxScales.coordinate_bounds X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_upper).2.1
  have hEN := (DeterminantBoxScales.coordinate_bounds X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_upper).2.1
  have hQNR := mul_le_mul_of_nonneg_right hQR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  obtain ⟨A, B, L₀, L₁, hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct, hupper, hlower, hpoints⟩ :=
      hcoords N hN M hM hMN X.D X.E X.D_ge_one X.E_ge_one (hDN.trans hQNR) (hEN.trans hQNR) k hk
  exact ⟨A, B, L₀, L₁, ⟨hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct, hupper, hlower, hpoints⟩⟩

end PaperP1.HorizontalGridCoordinateData
