module

public import PaperP1.Analysis.BinaryLatticeCoordinateBounds

/-! # Actual inverse integer coordinates in the reduced lattice boxes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedLatticeCoordinateBoxes

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BinaryLatticeCoordinateBounds PaperP1.BinaryBasisShear

theorem image_matrix_expansion (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (q : Fin 2 → ℤ) :
    realImage T (A.mulVec q) = combination (realImage T (fun i ↦ A i 0))
      (realImage T (fun i ↦ A i 1)) (q 0 : ℝ) (q 1 : ℝ) := by
  funext i
  simp only [realImage, combination, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Int.cast_add, Int.cast_mul]
  ring

theorem inverse_coordinate_expansion (T : Matrix (Fin 2) (Fin 2) ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (z : Fin 2 → ℤ) :
    realImage T z = combination (realImage T (fun i ↦ A i 0))
      (realImage T (fun i ↦ A i 1)) (B.mulVec z 0 : ℝ) (B.mulVec z 1 : ℝ) := by
  have hr := UnimodularBinaryCoordinates.reconstruct B A hAB z
  calc
    _ = realImage T (A.mulVec (B.mulVec z)) := congrArg (realImage T) hr.symm
    _ = _ := image_matrix_expansion T A (B.mulVec z)

theorem actual_coordinate_bounds (T : Matrix (Fin 2) (Fin 2) ℝ)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hdet : A.det = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hp : 0 < squareNorm (realImage T (fun i ↦ A i 0)))
    (horder : squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T (fun i ↦ A i 1)))
    (harea : 3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ A i 1))) ≤
      4 * T.det ^ 2) (z : Fin 2 → ℤ) (hbox : ∀ i, |realImage T z i| ≤ R) :
    |(B.mulVec z 0 : ℝ)| ≤ sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ∧
      |(B.mulVec z 1 : ℝ)| ≤ sideLength R (squareNorm (realImage T (fun i ↦ A i 1))) := by
  have ha : area (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) = T.det := by
    simpa only [hdet, Int.cast_one, mul_one] using image_area T A
  apply box_coordinate_bounds _ _ _ _ R hR hp horder (by simpa only [ha] using harea)
  intro i
  rw [← inverse_coordinate_expansion T A B hAB z]
  exact hbox i

theorem actual_side_controls (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (hBA : B * A = 1) (hdet : A.det = 1)
    (R : ℝ) (hR : 0 ≤ R)
    (hp : 0 < squareNorm (realImage T (fun i ↦ A i 0)))
    (horder : squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T (fun i ↦ A i 1)))
    (harea : 3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ A i 1))) ≤
      4 * T.det ^ 2) :
    sideLength R (squareNorm (realImage T (fun i ↦ A i 1))) ≤ sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ∧
      sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) * sideLength R (squareNorm (realImage T (fun i ↦ A i 1))) ≤
        4 * R ^ 2 / |T.det| ∧
      sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ≤ 2 * R * (inverseSize S + 1) ∧
      R ^ 2 ≤ sideLength R (squareNorm (realImage T (fun i ↦ A i 0))) ^ 2 * |T.det| := by
  have ha : area (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) = T.det := by
    simpa only [hdet, Int.cast_one, mul_one] using image_area T A
  have hh : 3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ A i 1))) ≤
      4 * area (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) ^ 2 := by simpa only [ha] using harea
  refine ⟨sideLength_order R _ _ hR hp horder, ?_, ?_, ?_⟩
  · simpa only [ha] using sideLength_product _ _ R hp horder hh
  · exact sideLength_inverse_bound R _ _ hR hp (inverseSize_nonnegative S)
      (BinaryReductionBounds.integer_energy_lower_bound T S hST _ (column_nonzero A B hBA 0))
  · exact sideLength_lower_square R _ _ _ hp horder harea

theorem one_le_largest_of_primitive (q : Fin 2 → ℤ)
    (hq : (q 0).natAbs.Coprime (q 1).natAbs) (L₀ L₁ : ℝ) (horder : L₁ ≤ L₀)
    (hbox : |(q 0 : ℝ)| ≤ L₀ ∧ |(q 1 : ℝ)| ≤ L₁) : 1 ≤ L₀ := by
  have hq0 := UnimodularBinaryCoordinates.primitive_nonzero q hq
  by_cases h0 : q 0 = 0
  · have h1 : q 1 ≠ 0 := by
      intro h1
      apply hq0
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hr : (1 : ℝ) ≤ |(q 1 : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact hr.trans (hbox.2.trans horder)
  · have hr : (1 : ℝ) ≤ |(q 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h0
    exact hr.trans hbox.1

end PaperP1.ReducedLatticeCoordinateBoxes
