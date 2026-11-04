module

public import PaperP1.Asymptotics.UniformLatticeCoordinateBoxes
public import PaperP1.Analysis.DeterminantRelativeIntervals

/-! # The actual real lattice matrix on a source relative interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalLattice

open PaperP1.BinaryLatticeMinimum PaperP1.DeterminantRelativeIntervals

def transform (D E M s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![M / D, -M * s / D; 0, 1 / E]

def inverse (D E M s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![D / M, s * E; 0, E]

theorem inverse_products (D E M s : ℝ) (hD : D ≠ 0) (hE : E ≠ 0) (hM : M ≠ 0) :
    transform D E M s * inverse D E M s = 1 ∧ inverse D E M s * transform D E M s = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [transform, inverse, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    field_simp [hD, hE, hM] <;> ring

theorem determinant (D E M s : ℝ) : (transform D E M s).det = M / (D * E) := by
  rw [Matrix.det_fin_two]
  change (M / D) * (1 / E) - (-M * s / D) * 0 = M / (D * E)
  rw [mul_zero, sub_zero, div_mul_div_comm, mul_one]

theorem image_formula (D E M s : ℝ) (z : Fin 2 → ℤ) :
    realImage (transform D E M s) z =
      ![(M / D) * ((z 0 : ℝ) - s * (z 1 : ℝ)), (z 1 : ℝ) / E] := by
  funext i
  fin_cases i <;> simp [realImage, transform, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem floor_residual_identity (M k : ℕ) (hM : 0 < M) (D E d e : ℝ)
    (hD : D ≠ 0) (hE : E ≠ 0) (he : e ≠ 0) :
    ((M : ℝ) / D) * (d - intervalCenter M D E k * e) =
      (e / E) * (scaledRatio M D E d e - k) := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  unfold intervalCenter scaledRatio
  field_simp [hD, hE, he, hMR]

theorem actual_point_box (M : ℕ) (hM : 0 < M) (D E : ℝ) (hD : 0 < D) (hE : 0 < E)
    (z : Fin 2 → ℤ) (hdlo : D ≤ (z 0 : ℝ)) (hdhi : (z 0 : ℝ) ≤ 2 * D)
    (helo : E ≤ (z 1 : ℝ)) (hehi : (z 1 : ℝ) ≤ 2 * E) :
    ∀ i, |realImage (transform D E M (intervalCenter M D E
      (intervalIndex M D E (z 0 : ℝ) (z 1 : ℝ)))) z i| ≤ 2 := by
  have he : 0 < (z 1 : ℝ) := hE.trans_le helo
  have hs := scaled_bounds M hD hE hdlo hdhi helo hehi
  have hnonnegative : 0 ≤ scaledRatio M D E (z 0 : ℝ) (z 1 : ℝ) := by
    have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith [hs.1]
  have hflo := Nat.floor_le hnonnegative
  have hfhi := Nat.lt_floor_add_one (scaledRatio M D E (z 0 : ℝ) (z 1 : ℝ))
  have hreslo : 0 ≤ scaledRatio M D E (z 0 : ℝ) (z 1 : ℝ) -
      intervalIndex M D E (z 0 : ℝ) (z 1 : ℝ) := by unfold intervalIndex; linarith
  have hreshi : scaledRatio M D E (z 0 : ℝ) (z 1 : ℝ) -
      intervalIndex M D E (z 0 : ℝ) (z 1 : ℝ) ≤ 1 := by unfold intervalIndex; linarith
  have heratio : 0 ≤ (z 1 : ℝ) / E := (div_pos he hE).le
  have heupper : (z 1 : ℝ) / E ≤ 2 := (div_le_iff₀ hE).mpr (by linarith only [hehi])
  intro i
  rw [image_formula]
  fin_cases i
  · change |((M : ℝ) / D) * ((z 0 : ℝ) - intervalCenter M D E
      (intervalIndex M D E (z 0 : ℝ) (z 1 : ℝ)) * (z 1 : ℝ))| ≤ 2
    rw [floor_residual_identity M _ hM D E _ _ hD.ne' hE.ne' he.ne']
    rw [abs_of_nonneg (mul_nonneg heratio hreslo)]
    nlinarith [mul_le_mul_of_nonneg_left hreshi heratio]
  · change |(z 1 : ℝ) / E| ≤ 2
    rw [abs_of_nonneg heratio]
    exact heupper

end PaperP1.RelativeIntervalLattice
