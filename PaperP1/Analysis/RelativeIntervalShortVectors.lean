module

public import PaperP1.Asymptotics.UniformRelativeIntervalCoordinates

/-! # Actual first-lattice vector coordinates and the integer-product residual -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalShortVectors

open PaperP1.RelativeIntervalLattice PaperP1.RelativeIntervalLatticeHeight
open PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BinaryLatticeCoordinateBounds

theorem coordinate_norm_bound (v : Fin 2 → ℝ) (i : Fin 2) : |v i| ≤ Real.sqrt (squareNorm v) := by
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (squareNorm_nonnegative v)]
  fin_cases i
  · change v 0 ^ 2 ≤ squareNorm v
    unfold squareNorm
    nlinarith [sq_nonneg (v 1)]
  · change v 1 ^ 2 ≤ squareNorm v
    unfold squareNorm
    nlinarith [sq_nonneg (v 0)]

theorem length_identity (P : ℝ) (hP : 0 < P) : Real.sqrt P * sideLength 2 P = 4 := by
  have hs : Real.sqrt P ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  calc
    _ = (4 / Real.sqrt P) * Real.sqrt P := by unfold sideLength; ring
    _ = 4 := div_mul_cancel₀ _ hs

theorem inverse_coordinates (D E M s : ℝ) (hD : D ≠ 0) (hE : E ≠ 0) (hM : M ≠ 0)
    (z : Fin 2 → ℤ) :
    (z 0 : ℝ) = (D / M) * realImage (transform D E M s) z 0 +
      (s * E) * realImage (transform D E M s) z 1 ∧
      (z 1 : ℝ) = E * realImage (transform D E M s) z 1 := by
  have hr := UnimodularBinaryCoordinates.reconstruct (transform D E M s) (inverse D E M s)
    (inverse_products D E M s hD hE hM).2 (fun i ↦ (z i : ℝ))
  change (inverse D E M s).mulVec (realImage (transform D E M s) z) = (fun i ↦ (z i : ℝ)) at hr
  constructor
  · simpa [inverse, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using (congrFun hr 0).symm
  · simpa [inverse, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using (congrFun hr 1).symm

theorem interval_residual_identity (M k : ℕ) (hM : 0 < M) (D E : ℝ) (hD : D ≠ 0) (hE : E ≠ 0)
    (z : Fin 2 → ℤ) :
    (z 1 : ℝ) * k - ((M : ℝ) * E / D) * (z 0 : ℝ) =
      -E * realImage (transform D E M (intervalCenter M D E k)) z 0 := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [image_formula]
  simp only [Matrix.cons_val_zero]
  unfold intervalCenter
  field_simp [hD, hE, hMR]
  ring

theorem source_vector_bounds (M k : ℕ) (hM : 1 ≤ M) (hk : k ≤ 2 * M)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E) (z : Fin 2 → ℤ) :
    let T := transform D E M (intervalCenter M D E k)
    |(z 0 : ℝ)| ≤ 3 * D * Real.sqrt (squareNorm (realImage T z)) ∧
      |(z 1 : ℝ)| ≤ E * Real.sqrt (squareNorm (realImage T z)) ∧
      |(z 1 : ℝ) * k - ((M : ℝ) * E / D) * (z 0 : ℝ)| ≤
        E * Real.sqrt (squareNorm (realImage T z)) := by
  have hMp : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMp
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  let s := intervalCenter M D E k
  let v := realImage (transform D E M s) z
  have hcenter := interval_center_range M k hMp hk D E hD hE
  have hse : s * E ≤ 2 * D := (le_div_iff₀ hE).mp hcenter.2
  have hdiv : D / (M : ℝ) ≤ D := (div_le_iff₀ hMR).mpr (by nlinarith)
  have hv := coordinate_norm_bound v
  have hcoordinates := inverse_coordinates D E M s hD.ne' hE.ne' hMR.ne' z
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoordinates.1]
    calc
      _ ≤ |D / (M : ℝ) * v 0| + |s * E * v 1| := abs_add_le _ _
      _ = (D / (M : ℝ)) * |v 0| + (s * E) * |v 1| := by
        rw [abs_mul, abs_mul, abs_of_pos (div_pos hD hMR), abs_of_nonneg (mul_nonneg hcenter.1 hE.le)]
      _ ≤ D * Real.sqrt (squareNorm v) + (2 * D) * Real.sqrt (squareNorm v) := by
        gcongr
        · exact hv 0
        · exact hv 1
      _ = _ := by ring
  · rw [hcoordinates.2, abs_mul, abs_of_pos hE]
    exact mul_le_mul_of_nonneg_left (hv 1) hE.le
  · rw [interval_residual_identity M k hMp D E hD.ne' hE.ne' z, abs_mul, abs_neg, abs_of_pos hE]
    exact mul_le_mul_of_nonneg_left (hv 0) hE.le

theorem scaled_vector_bounds (M k : ℕ) (hM : 1 ≤ M) (hk : k ≤ 2 * M)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E) (z : Fin 2 → ℤ) (hz : z ≠ 0) :
    let T := transform D E M (intervalCenter M D E k)
    let L := sideLength 2 (squareNorm (realImage T z))
    0 < L ∧ |(z 0 : ℝ)| ≤ 12 * D / L ∧ |(z 1 : ℝ)| ≤ 4 * E / L ∧
      |(z 1 : ℝ) * k - ((M : ℝ) * E / D) * (z 0 : ℝ)| ≤ 4 * E / L := by
  have hMp : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMp
  let T := transform D E M (intervalCenter M D E k)
  let S := inverse D E M (intervalCenter M D E k)
  have hST : S * T = 1 := (inverse_products D E M _ hD.ne' hE.ne' hMR.ne').2
  have hp := image_energy_positive T S hST z hz
  let L := sideLength 2 (squareNorm (realImage T z))
  have hL : 0 < L := by dsimp [L, sideLength]; positivity
  have hid : Real.sqrt (squareNorm (realImage T z)) * L = 4 := length_identity _ hp
  have hb := source_vector_bounds M k hM hk D E hD hE z
  refine ⟨hL, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hL).mpr
    calc
      _ ≤ (3 * D * Real.sqrt (squareNorm (realImage T z))) * L := mul_le_mul_of_nonneg_right hb.1 hL.le
      _ = _ := by rw [mul_assoc, hid]; ring
  · apply (le_div_iff₀ hL).mpr
    calc
      _ ≤ (E * Real.sqrt (squareNorm (realImage T z))) * L := mul_le_mul_of_nonneg_right hb.2.1 hL.le
      _ = _ := by rw [mul_assoc, hid]; ring
  · apply (le_div_iff₀ hL).mpr
    calc
      _ ≤ (E * Real.sqrt (squareNorm (realImage T z))) * L := mul_le_mul_of_nonneg_right hb.2.2 hL.le
      _ = _ := by rw [mul_assoc, hid]; ring

end PaperP1.RelativeIntervalShortVectors
