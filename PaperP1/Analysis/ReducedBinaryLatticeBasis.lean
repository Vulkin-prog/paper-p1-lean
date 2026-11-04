module

public import PaperP1.Arithmetic.BinaryBasisShear

/-! # Actual reduced unimodular bases of every invertible binary lattice -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedBinaryLatticeBasis

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryBasisShear

def reduced (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  A * shear (multiple (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)))

def reducedInverse (T : Matrix (Fin 2) (Fin 2) ℝ) (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  shear (-(multiple (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)))) * B

theorem reduced_inverse (T : Matrix (Fin 2) (Fin 2) ℝ) (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    reduced T A * reducedInverse T A B = 1 ∧ reducedInverse T A B * reduced T A = 1 :=
  sheared_inverse A B hAB hBA _

theorem reduced_det (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det = 1) :
    (reduced T A).det = 1 := by rw [reduced, Matrix.det_mul, hA, shear_det, one_mul]

theorem reduced_first (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    (fun i ↦ reduced T A i 0) = fun i ↦ A i 0 := first_column A _

theorem reduced_second_image (T : Matrix (Fin 2) (Fin 2) ℝ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    realImage T (fun i ↦ reduced T A i 1) =
      reduce (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) := sheared_image T A _

theorem reduced_geometry (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hBA : B * A = 1) (hA : A.det = 1)
    (hmin : ∀ w : Fin 2 → ℤ, w ≠ 0 →
      squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) :
    squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T (fun i ↦ reduced T A i 1)) ∧
      |scalarProduct (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ reduced T A i 1))| ≤
        squareNorm (realImage T (fun i ↦ A i 0)) / 2 ∧
      3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ reduced T A i 1))) ≤
        4 * T.det ^ 2 := by
  have hproducts := reduced_inverse T A B hAB hBA
  have hv := realImage_nonzero T S hST _ (column_nonzero A B hBA 0)
  have hshort := hmin _ (column_nonzero (reduced T A) (reducedInverse T A B) hproducts.2 1)
  refine ⟨hshort, ?_, ?_⟩
  · rw [reduced_second_image]
    exact reduced_projection_bound _ _ hv
  · rw [reduced_second_image] at hshort ⊢
    have harea : area (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) = T.det := by
      simpa only [hA, Int.cast_one, mul_one] using image_area T A
    simpa only [harea] using reduced_area_bound _ _ hv hshort

theorem exists_reduced_basis (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B = 1 ∧ B * A = 1 ∧ A.det = 1 ∧
      (∀ w : Fin 2 → ℤ, w ≠ 0 →
        squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) ∧
      0 < squareNorm (realImage T (fun i ↦ A i 0)) ∧
      squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T (fun i ↦ A i 1)) ∧
      |scalarProduct (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1))| ≤
        squareNorm (realImage T (fun i ↦ A i 0)) / 2 ∧
      3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ A i 1))) ≤
        4 * T.det ^ 2 := by
  obtain ⟨z, hz, hprimitive, hmin, _⟩ := PrimitiveShortestVector.exists_primitive_shortest T S hST
  obtain ⟨r, s, hbezout⟩ := (UnimodularBinaryCoordinates.primitive_iff_isCoprime z).mp hprimitive
  have hb : z 0 * r + z 1 * s = 1 := by linear_combination hbezout
  let A₀ := PrimitiveBinaryBasis.basis (z 0) (z 1) r s
  let B₀ := PrimitiveBinaryBasis.inverse (z 0) (z 1) r s
  have hfirst : (fun i ↦ A₀ i 0) = z := by funext i; fin_cases i <;> rfl
  have hAB := PrimitiveBinaryBasis.basis_inverse (z 0) (z 1) r s hb
  have hdet : A₀.det = 1 := primitive_basis_det _ _ _ _ hb
  have hminimal : ∀ w : Fin 2 → ℤ, w ≠ 0 →
      squareNorm (realImage T (fun i ↦ A₀ i 0)) ≤ squareNorm (realImage T w) := by
    simpa only [hfirst] using hmin
  have hgeometry := reduced_geometry T S hST A₀ B₀ hAB.1 hAB.2 hdet hminimal
  have hnew := reduced_inverse T A₀ B₀ hAB.1 hAB.2
  refine ⟨reduced T A₀, reducedInverse T A₀ B₀, hnew.1, hnew.2, reduced_det T A₀ hdet, ?_, ?_, ?_⟩
  · simpa only [reduced_first, hfirst] using hmin
  · simpa only [reduced_first, hfirst] using image_energy_positive T S hST z hz
  · simpa only [reduced_first] using hgeometry

end PaperP1.ReducedBinaryLatticeBasis
