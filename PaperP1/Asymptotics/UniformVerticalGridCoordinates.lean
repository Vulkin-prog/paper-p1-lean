module

public import PaperP1.Arithmetic.VerticalGridMatrices
public import PaperP1.Asymptotics.UniformRelativeGridCoordinates

/-! # Actual polynomial-height reduced coordinates, chosen once per vertical grid index -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformVerticalGridCoordinates

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
open PaperP1.EffectiveSourceCoordinates PaperP1.BinaryLatticeMinimum
open PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeCoordinateBounds PaperP1.VerticalGridMatrices

theorem uniform_vertical_coordinates (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ, ∀ q : ℕ, q ≤ 4 * M →
      let R := 2 * (49 + 16 / ρ)
      let T := gridTransform X M q
      ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ,
        L₀ = sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ∧
        L₁ = sideLength R (squareNorm (realImage T (fun i ↦ A i 1))) ∧
        A * B = 1 ∧ B * A = 1 ∧ A.det = 1 ∧
        (∀ i j, |A i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧ (∀ i j, |B i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        (∀ w : Fin 2 → ℤ, w ≠ 0 →
          squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) ∧
        0 ≤ L₁ ∧ L₁ ≤ L₀ ∧
        L₀ * L₁ ≤ 4 * R ^ 2 * C ^ 2 * (X.U * X.V) / (ρ ^ 2 * M) ∧
        L₀ ≤ 2 * R * (((2 * (N ^ 2) ^ 2 : ℕ) : ℝ) + 1) ∧
        R ^ 2 * C ^ 2 * (scale N X.c₁ X.D * scale N X.c₂ X.E) / M ≤ L₀ ^ 2 ∧
        ∀ h : ℤ, (M : ℝ) * |(h : ℝ)| ≤ N → ∀ S : Finset Quad, SignedPopulation X h S →
          ∀ p ∈ S, QuadraticIntervalGrid.grid M (intervalIndex M X.D X.E p.1.1 p.1.2) = q →
          |(B.mulVec ![(p.2.2 : ℤ), (p.2.1 : ℤ)] 0 : ℝ)| ≤ L₀ ∧
            |(B.mulVec ![(p.2.2 : ℤ), (p.2.1 : ℤ)] 1 : ℝ)| ≤ L₁ := by
  let Q := ⌈2 * C⌉₊ + 1
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hQR : 2 * C ≤ (Q : ℝ) := by
    have hh := Nat.le_ceil (2 * C)
    dsimp [Q]
    push_cast
    linarith
  obtain ⟨κ, N₀, hcoords⟩ := UniformRelativeGridCoordinates.uniform_grid_coordinates Q hQ
  refine ⟨κ, N₀, ?_⟩
  intro N hN M hM hMN δ X q hq
  have hNp : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hNp
  have hscales := inflated_scale_bounds X hNp hC
  let U := scale N X.c₁ X.D
  let V := scale N X.c₂ X.E
  let R := 2 * (49 + 16 / ρ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hCq := mul_le_mul_of_nonneg_right hQR hn.le
  have hDq : 2 * C * V ≤ (Q : ℝ) * N := hscales.2.2.1.trans hCq
  have hEq : C * U ≤ (Q : ℝ) * N := by
    have hh : C ≤ (Q : ℝ) := by linarith
    exact hscales.2.2.2.trans (mul_le_mul_of_nonneg_right hh hn.le)
  obtain ⟨A, B, L₀, L₁, hL₀, hL₁, hAB, hBA, hdet, hA, hB, hmin,
    hnonnegative, horder, hproduct, hupper, hlower, hpoints⟩ :=
    hcoords N hN (2 * M) (by omega) hMN (2 * C * V) (C * U)
      hscales.1 hscales.2.1 hDq hEq q (by omega) R hR
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hfactor : 4 * R ^ 2 * ((2 * C * V) * (C * U)) / ((2 * M : ℕ) : ℝ) =
      (4 * R ^ 2 * C ^ 2 / M) * (U * V) := by push_cast; field_simp
  have hproduct' : L₀ * L₁ ≤ 4 * R ^ 2 * C ^ 2 * (X.U * X.V) / (ρ ^ 2 * M) := by
    calc
      _ ≤ 4 * R ^ 2 * ((2 * C * V) * (C * U)) / ((2 * M : ℕ) : ℝ) := hproduct
      _ = (4 * R ^ 2 * C ^ 2 / M) * (U * V) := hfactor
      _ ≤ (4 * R ^ 2 * C ^ 2 / M) * ((X.U * X.V) / ρ ^ 2) :=
        mul_le_mul_of_nonneg_left (effective_pair_product_bound X hNp hρ) (by positivity)
      _ = _ := by ring
  have hlower' : R ^ 2 * C ^ 2 * (U * V) / M ≤ L₀ ^ 2 := by
    convert hlower using 1
    push_cast
    field_simp
  refine ⟨A, B, L₀, L₁, ?_, ?_, hAB, hBA, hdet, hA, hB, ?_,
    hnonnegative, horder, hproduct', hupper, hlower', ?_⟩
  · simpa only [gridTransform, Nat.cast_mul, Nat.cast_ofNat] using hL₀
  · simpa only [gridTransform, Nat.cast_mul, Nat.cast_ofNat] using hL₁
  · simpa only [gridTransform, Nat.cast_mul, Nat.cast_ofNat] using hmin
  · intro h hMh S hS p hp hgrid
    apply hpoints ![(p.2.2 : ℤ), (p.2.1 : ℤ)]
    have hb := ActualVerticalLattice.actual_point_box X hNp hC hρ M (by omega) h hMh S hS p hp
    rw [actual_transform_eq, hgrid] at hb
    simpa only [gridTransform, Nat.cast_mul, Nat.cast_ofNat] using hb

end PaperP1.UniformVerticalGridCoordinates
