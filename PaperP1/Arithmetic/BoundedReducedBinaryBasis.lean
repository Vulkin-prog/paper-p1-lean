module

public import PaperP1.Analysis.BinaryLatticeEntryBounds

/-! # Actual reduced unimodular bases with explicit polynomial entry heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedReducedBinaryBasis

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction PaperP1.BinaryReductionBounds
open PaperP1.BinaryLatticeEntryBounds PaperP1.BinaryBasisShear PaperP1.ReducedBinaryLatticeBasis

def vectorHeight (J : ℕ) : ℕ := 4 * J ^ 4 + 1

def completionHeight (J : ℕ) : ℕ := vectorHeight J ^ 2 + vectorHeight J + 1

def projectionHeight (J : ℕ) : ℕ :=
  2 * J ^ 2 * (2 * J ^ 2 + 8 * J ^ 2 * completionHeight J ^ 2) + 1

def basisHeight (J : ℕ) : ℕ := 2 * completionHeight J * (projectionHeight J + 1)

theorem projection_height_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) (J : ℕ)
    (hT : ∀ i j, |T i j| ≤ (J : ℝ)) (hS : ∀ i j, |S i j| ≤ (J : ℝ))
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (hBA : B * A = 1)
    (hA : ∀ i j, |A i j| ≤ (completionHeight J : ℤ))
    (hmin : ∀ w : Fin 2 → ℤ, w ≠ 0 →
      squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) :
    |multiple (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1))| ≤ (projectionHeight J : ℤ) := by
  have hu : (![1, 0] : Fin 2 → ℤ) ≠ 0 := by intro h; have h0 := congrFun h 0; norm_num at h0
  have hP := (hmin _ hu).trans (candidate_energy_bound T J hT)
  have hQ := image_energy_bound T J (completionHeight J) (fun i ↦ A i 1) hT (fun i ↦ hA i 1)
  have hK := inverseSize_bound S J hS
  have hrounded := lattice_multiple_bound T S hST (fun i ↦ A i 0) (fun i ↦ A i 1) (column_nonzero A B hBA 0)
  have hfinal : |(multiple (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1)) : ℝ)| ≤
      (projectionHeight J : ℝ) := by
    calc
      _ ≤ inverseSize S * (squareNorm (realImage T (fun i ↦ A i 0)) +
          squareNorm (realImage T (fun i ↦ A i 1))) + 1 := hrounded
      _ ≤ ((2 * J ^ 2 : ℕ) : ℝ) * (((2 * J ^ 2 : ℕ) : ℝ) +
          ((8 * J ^ 2 * completionHeight J ^ 2 : ℕ) : ℝ)) + 1 := by
        gcongr
        exact add_nonneg (squareNorm_nonnegative _) (squareNorm_nonnegative _)
      _ = _ := by simp only [projectionHeight, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  exact_mod_cast hfinal

theorem exists_bounded_reduced_basis (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) (J : ℕ)
    (hT : ∀ i j, |T i j| ≤ (J : ℝ)) (hS : ∀ i j, |S i j| ≤ (J : ℝ)) :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B = 1 ∧ B * A = 1 ∧ A.det = 1 ∧
      (∀ i j, |A i j| ≤ (basisHeight J : ℤ)) ∧ (∀ i j, |B i j| ≤ (basisHeight J : ℤ)) ∧
      (∀ w : Fin 2 → ℤ, w ≠ 0 →
        squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T w)) ∧
      0 < squareNorm (realImage T (fun i ↦ A i 0)) ∧
      squareNorm (realImage T (fun i ↦ A i 0)) ≤ squareNorm (realImage T (fun i ↦ A i 1)) ∧
      |scalarProduct (realImage T (fun i ↦ A i 0)) (realImage T (fun i ↦ A i 1))| ≤
        squareNorm (realImage T (fun i ↦ A i 0)) / 2 ∧
      3 * (squareNorm (realImage T (fun i ↦ A i 0)) * squareNorm (realImage T (fun i ↦ A i 1))) ≤
        4 * T.det ^ 2 := by
  obtain ⟨z, hz, hprimitive, hmin, _⟩ := PrimitiveShortestVector.exists_primitive_shortest T S hST
  have hzheight : ∀ i, |z i| ≤ (vectorHeight J : ℤ) := shortest_height_bound T S hST J hT hS z hmin
  obtain ⟨r, s, hb, hr, hs⟩ := PrimitiveBinaryBasis.bounded_bezout (z 0) (z 1) (vectorHeight J)
    ((UnimodularBinaryCoordinates.primitive_iff_isCoprime z).mp hprimitive) (hzheight 0) (hzheight 1)
  let A₀ := PrimitiveBinaryBasis.basis (z 0) (z 1) r s
  let B₀ := PrimitiveBinaryBasis.inverse (z 0) (z 1) r s
  have hfirst : (fun i ↦ A₀ i 0) = z := by funext i; fin_cases i <;> rfl
  have hAB := PrimitiveBinaryBasis.basis_inverse (z 0) (z 1) r s hb
  have hdet : A₀.det = 1 := primitive_basis_det _ _ _ _ hb
  have hbase := PrimitiveBinaryBasis.basis_height (z 0) (z 1) r s (vectorHeight J)
    (hzheight 0) (hzheight 1) hr hs
  have hA₀ : ∀ i j, |A₀ i j| ≤ (completionHeight J : ℤ) := hbase.1
  have hB₀ : ∀ i j, |B₀ i j| ≤ (completionHeight J : ℤ) := hbase.2
  have hminimal : ∀ w : Fin 2 → ℤ, w ≠ 0 →
      squareNorm (realImage T (fun i ↦ A₀ i 0)) ≤ squareNorm (realImage T w) := by
    simpa only [hfirst] using hmin
  have hprojection := projection_height_bound T S hST J hT hS A₀ B₀ hAB.2 hA₀ hminimal
  have hheight := BinaryMatrixProductHeight.reduced_heights T A₀ B₀ (completionHeight J) (projectionHeight J)
    hA₀ hB₀ hprojection
  have hgeometry := reduced_geometry T S hST A₀ B₀ hAB.1 hAB.2 hdet hminimal
  have hnew := reduced_inverse T A₀ B₀ hAB.1 hAB.2
  refine ⟨reduced T A₀, reducedInverse T A₀ B₀, hnew.1, hnew.2, reduced_det T A₀ hdet,
    hheight.1, hheight.2, ?_, ?_, ?_⟩
  · simpa only [reduced_first, hfirst] using hmin
  · simpa only [reduced_first, hfirst] using image_energy_positive T S hST z hz
  · simpa only [reduced_first] using hgeometry

end PaperP1.BoundedReducedBinaryBasis
