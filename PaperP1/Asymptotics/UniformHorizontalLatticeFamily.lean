module

public import PaperP1.Asymptotics.HorizontalGridCoordinateData
public import PaperP1.Asymptotics.RelativeIntervalSideSum

/-! # One actual horizontal basis family has both point coordinates and the complete side sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformHorizontalLatticeFamily

open Finset PaperP1.DeterminantSourceBox PaperP1.HorizontalGridCoordinateData
open PaperP1.DeterminantRelativeIntervals

theorem uniform_family_sum (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ M : ℕ, 4 ≤ M → M ≤ N →
      ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ,
      ∃ A B : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℕ → ℝ,
        (∀ k : ℕ, k ≤ 2 * M → Data X κ M k (A k) (B k) (L₀ k) (L₁ k)) ∧
        ∀ I : Finset ℕ, I ⊆ intervalIndices M → (∀ k ∈ I, (M : ℝ) / 4 ≤ k) →
          (∑ k ∈ I, L₀ k) ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (X.D * X.E * M) + 32 * X.E + 8 * X.D := by
  classical
  obtain ⟨κ, NC, hcoords⟩ := uniform_data C hC
  obtain ⟨NS, hsum⟩ := RelativeIntervalSideSum.uniform_first_lattice_sum κ ε hε
  refine ⟨κ, max NC NS, ?_⟩
  intro N hN M hM hMN ρ δ X
  have hchoice : ∀ k : ℕ, ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ : ℝ,
      Data X κ M (min k (2 * M)) A B L₀ L₁ := by
    intro k
    exact hcoords N (by omega) M hM hMN ρ δ X (min k (2 * M)) (min_le_right _ _)
  choose A B L₀ L₁ hdata using hchoice
  have hvalid : ∀ k : ℕ, k ≤ 2 * M → Data X κ M k (A k) (B k) (L₀ k) (L₁ k) := by
    intro k hk
    simpa only [min_eq_left hk] using hdata k
  refine ⟨A, B, L₀, L₁, hvalid, ?_⟩
  intro I hI hlow
  let z := fun k i ↦ A k i 0
  have hprimitive : ∀ k ∈ I, (z k 0).natAbs.Coprime (z k 1).natAbs := by
    intro k hk
    exact PrimitiveBinaryColumns.column_primitive (A k) (B k)
      (hvalid k (mem_Icc.mp (hI hk)).2).left_inverse 0
  have hheight : ∀ k ∈ I, (z k 1).natAbs ≤ N ^ κ := by
    intro k hk
    have hh := (hvalid k (mem_Icc.mp (hI hk)).2).basis_height 1 0
    have habs : ((A k 1 0).natAbs : ℤ) ≤ ((N ^ κ : ℕ) : ℤ) := by
      simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast habs
  have hD : 0 < X.D := by linarith [X.D_ge_one]
  have hE : 0 < X.E := by linarith [X.E_ge_one]
  have hb := hsum N (by omega) M (by omega) hMN X.D X.E hD hE I hI hlow z hprimitive hheight
  calc
    _ = ∑ k ∈ I, PaperP1.BinaryLatticeCoordinateBounds.sideLength 2
        (PaperP1.BinaryEuclideanReduction.squareNorm
          (PaperP1.BinaryLatticeMinimum.realImage
            (PaperP1.RelativeIntervalLattice.transform X.D X.E M (intervalCenter M X.D X.E k)) (z k))) := by
      apply sum_congr rfl
      intro k hk
      exact (hvalid k (mem_Icc.mp (hI hk)).2).large_eq
    _ ≤ _ := hb

end PaperP1.UniformHorizontalLatticeFamily
