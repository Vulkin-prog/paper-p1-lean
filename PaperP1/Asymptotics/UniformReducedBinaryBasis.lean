module

public import PaperP1.Asymptotics.ReducedBasisPolynomialBound

/-! # One actual reduced-basis height exponent before all moving real lattice matrices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformReducedBinaryBasis

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BoundedReducedBinaryBasis PaperP1.ReducedBasisPolynomialBound

theorem uniform_reduced_basis (μ : ℕ) :
    ∃ κ N₀ : ℕ, ∀ N ≥ N₀, ∀ T S : Matrix (Fin 2) (Fin 2) ℝ, S * T = 1 →
      (∀ i j, |T i j| ≤ ((N ^ μ : ℕ) : ℝ)) → (∀ i j, |S i j| ≤ ((N ^ μ : ℕ) : ℝ)) →
      ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B = 1 ∧ B * A = 1 ∧ A.det = 1 ∧
        (∀ i j, |A i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧ (∀ i j, |B i j| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
        (∀ w : Fin 2 → ℤ, w ≠ 0 →
          squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) ∧
        0 < squareNorm (realImage T (fun i ↦ A i 0)) ∧
        squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T (fun i ↦ A i 1)) ∧
        |scalarProduct (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1))| ≤
          squareNorm (realImage T (fun i ↦ A i 0)) / 2 ∧
        3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ A i 1))) ≤
          4 * T.det ^ 2 := by
  refine ⟨60 * (μ + 1), 2, ?_⟩
  intro N hN T S hST hT hS
  let J := N ^ (μ + 1)
  have hN0 : 0 < N := by omega
  have hN1 : 1 ≤ N ^ μ := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hNJ : N ≤ J := by
    simpa only [J, pow_succ', mul_one] using Nat.mul_le_mul_left N hN1
  have hJ : 2 ≤ J := hN.trans hNJ
  have hμ : N ^ μ ≤ J := Nat.pow_le_pow_right (by omega) (by omega)
  have hTJ : ∀ i j, |T i j| ≤ (J : ℝ) := fun i j ↦ (hT i j).trans (by exact_mod_cast hμ)
  have hSJ : ∀ i j, |S i j| ≤ (J : ℝ) := fun i j ↦ (hS i j).trans (by exact_mod_cast hμ)
  have hheight : basisHeight J ≤ N ^ (60 * (μ + 1)) := by
    calc
      _ ≤ J ^ 60 := basis_height_bound J hJ
      _ = _ := by dsimp [J]; rw [← pow_mul, Nat.mul_comm (μ + 1) 60]
  obtain ⟨A, B, hAB, hBA, hdet, hA, hB, hmin, hpositive, hshort, hprojection, harea⟩ :=
    exists_bounded_reduced_basis T S hST J hTJ hSJ
  refine ⟨A, B, hAB, hBA, hdet, ?_, ?_, hmin, hpositive, hshort, hprojection, harea⟩
  · intro i j
    exact (hA i j).trans (by exact_mod_cast hheight)
  · intro i j
    exact (hB i j).trans (by exact_mod_cast hheight)

end PaperP1.UniformReducedBinaryBasis
