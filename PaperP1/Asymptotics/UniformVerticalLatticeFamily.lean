module

public import PaperP1.Asymptotics.VerticalGridCoordinateData
public import PaperP1.Asymptotics.EffectiveVerticalSideSum
public import PaperP1.Arithmetic.PrimitiveBinaryColumns

/-! # One actual vertical basis family with simultaneous point coordinates and source-scale side sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformVerticalLatticeFamily

open Finset PaperP1.DeterminantSourceBox PaperP1.VerticalGridCoordinateData
open PaperP1.QuadraticIntervalGrid

theorem uniform_family_sum (ε C ρ : ℝ) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 32 ≤ M → 2 * M ≤ N →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ,
      ∃ A B : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℕ → ℝ,
        (∀ q : ℕ, q ≤ 4 * M → Data X κ M q (A q) (B q) (L₀ q) (L₁ q)) ∧
        ∀ I : Finset ℕ, (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) →
          (∑ k ∈ I, L₀ (grid M k)) ≤
            (512 * (2 * (49 + 16 / ρ)) * C / ρ) * (N : ℝ) ^ ε *
              (Real.sqrt (X.U * X.V * M) + X.U + X.V) := by
  classical
  obtain ⟨κ, NC, hcoords⟩ := uniform_data C ρ hC hρ
  obtain ⟨NS, hsum⟩ := EffectiveVerticalSideSum.uniform_original_scale_sum κ ε C ρ hε hC hρ
  refine ⟨κ, max NC NS, ?_⟩
  intro N hN M hM hMN δ X
  have hchoice : ∀ q : ℕ, ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ,
      Data X κ M (min q (4 * M)) A B L₀ L₁ := by
    intro q
    exact hcoords N (by omega) M hM hMN δ X (min q (4 * M)) (min_le_right _ _)
  choose A B L₀ L₁ hdata using hchoice
  have hvalid : ∀ q : ℕ, q ≤ 4 * M → Data X κ M q (A q) (B q) (L₀ q) (L₁ q) := by
    intro q hq
    simpa only [min_eq_left hq] using hdata q
  refine ⟨A, B, L₀, L₁, hvalid, ?_⟩
  intro I hlow hupper
  have hrange : ∀ q ∈ I.image (grid M), q ≤ 4 * M := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
    exact grid_upper M k (by omega) (hupper k hk)
  let z := fun q i ↦ A q i 0
  have hprimitive : ∀ q ∈ I.image (grid M), (z q 0).natAbs.Coprime (z q 1).natAbs := by
    intro q hq
    exact PrimitiveBinaryColumns.column_primitive (A q) (B q) (hvalid q (hrange q hq)).left_inverse 0
  have hheight : ∀ q ∈ I.image (grid M), (z q 1).natAbs ≤ N ^ κ := by
    intro q hq
    have hh := (hvalid q (hrange q hq)).basis_height 1 0
    have habs : ((A q 1 0).natAbs : ℤ) ≤ ((N ^ κ : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast habs
  have hb := hsum N (by omega) M hM hMN δ X I hlow hupper z hprimitive hheight
  calc
    _ = ∑ k ∈ I, PaperP1.BinaryLatticeCoordinateBounds.sideLength (2 * (49 + 16 / ρ))
        (PaperP1.BinaryEuclideanReduction.squareNorm
          (PaperP1.BinaryLatticeMinimum.realImage (PaperP1.VerticalGridMatrices.gridTransform X M (grid M k)) (z (grid M k)))) := by
      apply sum_congr rfl
      intro k hk
      exact (hvalid (grid M k) (grid_upper M k (by omega) (hupper k hk))).large_eq
    _ ≤ _ := hb

end PaperP1.UniformVerticalLatticeFamily
