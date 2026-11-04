module

public import PaperP1.Arithmetic.PrimitiveShortestVector
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Actual integer basis shears and their exact real lattice geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryBasisShear

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction

def shear (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, -k; 0, 1]

theorem shear_inverse (k : ℤ) : shear k * shear (-k) = 1 ∧ shear (-k) * shear k = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [shear, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem shear_det (k : ℤ) : (shear k).det = 1 := by simp [shear, Matrix.det_fin_two]

theorem first_column (A : Matrix (Fin 2) (Fin 2) ℤ) (k : ℤ) :
    (fun i ↦ (A * shear k) i 0) = fun i ↦ A i 0 := by
  funext i
  simp [shear, Matrix.mul_apply, Fin.sum_univ_two]

theorem second_column (A : Matrix (Fin 2) (Fin 2) ℤ) (k : ℤ) :
    (fun i ↦ (A * shear k) i 1) = fun i ↦ A i 1 - k * A i 0 := by
  funext i
  simp [shear, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sheared_inverse (A B : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hBA : B * A = 1)
    (k : ℤ) : (A * shear k) * (shear (-k) * B) = 1 ∧ (shear (-k) * B) * (A * shear k) = 1 := by
  constructor
  · calc
      _ = A * (shear k * shear (-k)) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(shear_inverse k).1, Matrix.mul_one, hAB]
  · calc
      _ = shear (-k) * (B * A) * shear k := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.mul_one, (shear_inverse k).2]

theorem column_nonzero (A B : Matrix (Fin 2) (Fin 2) ℤ) (hBA : B * A = 1) (j : Fin 2) :
    (fun i ↦ A i j) ≠ 0 := by
  intro h
  have hc : A.col j = 0 := by funext i; exact congrFun h i
  have hs : Pi.single j (1 : ℤ) = 0 :=
    UnimodularBinaryCoordinates.coordinate_injective A B hBA
      (by simpa only [Matrix.mulVec_single_one, Matrix.mulVec_zero] using hc)
  have hj := congrFun hs j
  simp at hj

theorem sheared_image (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) (k : ℤ) :
    realImage T (fun i ↦ (A * shear k) i 1) =
      fun i ↦ realImage T (fun j ↦ A j 1) i - (k : ℝ) * realImage T (fun j ↦ A j 0) i := by
  rw [second_column]
  funext i
  simp only [realImage, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Int.cast_sub, Int.cast_mul]
  ring

theorem image_area (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    area (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) = T.det * (A.det : ℝ) := by
  simp only [area, realImage, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.det_fin_two, Int.cast_sub, Int.cast_mul]
  ring

theorem primitive_basis_det (p q r s : ℤ) (h : p * r + q * s = 1) :
    (PrimitiveBinaryBasis.basis p q r s).det = 1 := by
  norm_num [PrimitiveBinaryBasis.basis, Matrix.det_fin_two]
  nlinarith

end PaperP1.BinaryBasisShear
