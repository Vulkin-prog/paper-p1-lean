module

public import PaperP1.Arithmetic.BinaryMatrixProductHeight

/-! # Explicit lattice length and shortest-coordinate bounds from matrix entries -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryLatticeEntryBounds

open PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction

theorem square_of_abs_bound (x : ℝ) (H : ℕ) (hx : |x| ≤ (H : ℝ)) : x ^ 2 ≤ (H : ℝ) ^ 2 := by
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2

theorem squareNorm_bound (v : Fin 2 → ℝ) (H : ℕ) (hv : ∀ i, |v i| ≤ (H : ℝ)) :
    squareNorm v ≤ ((2 * H ^ 2 : ℕ) : ℝ) := by
  have h0 := square_of_abs_bound (v 0) H (hv 0)
  have h1 := square_of_abs_bound (v 1) H (hv 1)
  unfold squareNorm
  push_cast
  linarith

theorem inverseSize_bound (S : Matrix (Fin 2) (Fin 2) ℝ) (J : ℕ)
    (hS : ∀ i j, |S i j| ≤ (J : ℝ)) : inverseSize S ≤ ((2 * J ^ 2 : ℕ) : ℝ) :=
  max_le (squareNorm_bound (S 0) J (hS 0)) (squareNorm_bound (S 1) J (hS 1))

theorem candidate_energy_bound (T : Matrix (Fin 2) (Fin 2) ℝ) (J : ℕ)
    (hT : ∀ i j, |T i j| ≤ (J : ℝ)) :
    squareNorm (realImage T ![1, 0]) ≤ ((2 * J ^ 2 : ℕ) : ℝ) := by
  have he : realImage T (![1, 0] : Fin 2 → ℤ) = fun i ↦ T i 0 := by
    funext i
    simp [realImage, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [he]
  exact squareNorm_bound _ J (fun i ↦ hT i 0)

theorem image_coordinate_bound (T : Matrix (Fin 2) (Fin 2) ℝ) (J H : ℕ) (z : Fin 2 → ℤ)
    (hT : ∀ i j, |T i j| ≤ (J : ℝ)) (hz : ∀ i, |z i| ≤ (H : ℤ)) :
    ∀ i, |realImage T z i| ≤ ((2 * J * H : ℕ) : ℝ) := by
  have hzR : ∀ i, |(z i : ℝ)| ≤ (H : ℝ) := by intro i; exact_mod_cast hz i
  intro i
  simp only [realImage, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  calc
    _ ≤ |T i 0 * (z 0 : ℝ)| + |T i 1 * (z 1 : ℝ)| := abs_add_le _ _
    _ = |T i 0| * |(z 0 : ℝ)| + |T i 1| * |(z 1 : ℝ)| := by rw [abs_mul, abs_mul]
    _ ≤ (J : ℝ) * H + (J : ℝ) * H := by
      gcongr
      · exact hT i 0
      · exact hzR 0
      · exact hT i 1
      · exact hzR 1
    _ = _ := by push_cast; ring

theorem image_energy_bound (T : Matrix (Fin 2) (Fin 2) ℝ) (J H : ℕ) (z : Fin 2 → ℤ)
    (hT : ∀ i j, |T i j| ≤ (J : ℝ)) (hz : ∀ i, |z i| ≤ (H : ℤ)) :
    squareNorm (realImage T z) ≤ ((8 * J ^ 2 * H ^ 2 : ℕ) : ℝ) := by
  calc
    _ ≤ ((2 * (2 * J * H) ^ 2 : ℕ) : ℝ) := squareNorm_bound _ _ (image_coordinate_bound T J H z hT hz)
    _ = _ := by push_cast; ring

theorem shortest_height_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) (J : ℕ)
    (hT : ∀ i j, |T i j| ≤ (J : ℝ)) (hS : ∀ i j, |S i j| ≤ (J : ℝ)) (z : Fin 2 → ℤ)
    (hmin : ∀ w : Fin 2 → ℤ, w ≠ 0 → squareNorm (realImage T z) ≤ squareNorm (realImage T w)) :
    ∀ i, |z i| ≤ ((4 * J ^ 4 + 1 : ℕ) : ℤ) := by
  have hK := inverseSize_bound S J hS
  have hC := candidate_energy_bound T J hT
  have hprod := mul_le_mul hK hC (squareNorm_nonnegative _) (by positivity : (0 : ℝ) ≤ (2 * J ^ 2 : ℕ))
  have hceil : ⌈inverseSize S * squareNorm (realImage T ![1, 0]) + 1⌉ ≤ ((4 * J ^ 4 + 1 : ℕ) : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast at hprod ⊢
    nlinarith
  intro i
  exact (PrimitiveShortestVector.shortest_coordinate_bound T S hST z hmin i).trans hceil

end PaperP1.BinaryLatticeEntryBounds
