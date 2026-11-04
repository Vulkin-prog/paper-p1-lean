module

public import PaperP1.Analysis.ReducedBinaryLatticeBasis

/-! # Quantitative bounds on the actual nearest-integer reduction coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryReductionBounds

open PaperP1.BinaryEuclideanReduction PaperP1.BinaryLatticeMinimum

theorem scalar_product_bound (v w : Fin 2 → ℝ) :
    |scalarProduct v w| ≤ (squareNorm v + squareNorm w) / 2 := by
  have hminus := squareNorm_nonnegative (fun i ↦ v i - w i)
  have hplus := squareNorm_nonnegative (fun i ↦ v i + w i)
  apply abs_le.mpr
  unfold squareNorm scalarProduct at *
  constructor <;> nlinarith

theorem integer_energy_lower_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z : Fin 2 → ℤ) (hz : z ≠ 0) : 1 ≤ inverseSize S * squareNorm (realImage T z) := by
  have hex : ∃ i, z i ≠ 0 := by
    by_contra h
    apply hz
    funext i
    simpa only [not_not, Pi.zero_apply] using (not_exists.mp h) i
  obtain ⟨i, hi⟩ := hex
  have hZ := Int.one_le_abs hi
  have hR : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast hZ
  have hsq : (1 : ℝ) ≤ (z i : ℝ) ^ 2 := by nlinarith [sq_abs (z i : ℝ)]
  exact hsq.trans (coordinate_square_bound T S hST z i)

theorem round_absolute (x : ℝ) : |(round x : ℝ)| ≤ |x| + 1 := by
  have hr := abs_sub_round x
  calc
    _ = |((round x : ℝ) - x) + x| := by congr 1; ring
    _ ≤ |(round x : ℝ) - x| + |x| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) + |x| := by rw [abs_sub_comm]; linarith only [hr]
    _ ≤ _ := by linarith

theorem multiple_bound (v w : Fin 2 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hp : 0 < squareNorm v) (hKP : 1 ≤ K * squareNorm v) :
    |(multiple v w : ℝ)| ≤ K * (squareNorm v + squareNorm w) + 1 := by
  have hratio : |scalarProduct v w / squareNorm v| ≤ K * |scalarProduct v w| := by
    rw [abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    have h := mul_le_mul_of_nonneg_right hKP (abs_nonneg (scalarProduct v w))
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have hdot := mul_le_mul_of_nonneg_left (scalar_product_bound v w) hK
  have hround := round_absolute (scalarProduct v w / squareNorm v)
  change |(multiple v w : ℝ)| ≤ _ at hround
  have hnonnegative := mul_nonneg hK (add_nonneg (squareNorm_nonnegative v) (squareNorm_nonnegative w))
  nlinarith

theorem lattice_multiple_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z u : Fin 2 → ℤ) (hz : z ≠ 0) :
    |(multiple (realImage T z) (realImage T u) : ℝ)| ≤
      inverseSize S * (squareNorm (realImage T z) + squareNorm (realImage T u)) + 1 :=
  multiple_bound _ _ _ (inverseSize_nonnegative S) (image_energy_positive T S hST z hz)
    (integer_energy_lower_bound T S hST z hz)

end PaperP1.BinaryReductionBounds
