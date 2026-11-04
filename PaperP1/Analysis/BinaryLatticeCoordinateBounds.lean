module

public import PaperP1.Analysis.BinaryLatticeEntryBounds
public import Mathlib.Analysis.Real.Sqrt

/-! # Exact coordinate boxes and determinant bounds for a reduced binary basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryLatticeCoordinateBounds

open PaperP1.BinaryEuclideanReduction

def combination (v w : Fin 2 → ℝ) (c d : ℝ) : Fin 2 → ℝ := fun i ↦ c * v i + d * w i

def sideLength (R P : ℝ) : ℝ := 2 * R / Real.sqrt P

theorem cramer_first (v w : Fin 2 → ℝ) (c d : ℝ) : area (combination v w c d) w = c * area v w := by
  unfold area combination
  ring

theorem cramer_second (v w : Fin 2 → ℝ) (c d : ℝ) : area v (combination v w c d) = d * area v w := by
  unfold area combination
  ring

theorem area_length_bound (v w : Fin 2 → ℝ) :
    |area v w| ≤ Real.sqrt (squareNorm v) * Real.sqrt (squareNorm w) := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (squareNorm_nonnegative v), Real.sq_sqrt (squareNorm_nonnegative w)]
  have hg := gram_identity v w
  nlinarith [sq_nonneg (scalarProduct v w)]

theorem coordinate_square_bounds (v w : Fin 2 → ℝ) (c d : ℝ)
    (hp : 0 < squareNorm v) (horder : squareNorm v ≤ squareNorm w)
    (harea : 3 * (squareNorm v * squareNorm w) ≤ 4 * area v w ^ 2) :
    3 * c ^ 2 * squareNorm v ≤ 4 * squareNorm (combination v w c d) ∧
      3 * d ^ 2 * squareNorm w ≤ 4 * squareNorm (combination v w c d) := by
  have hq : 0 < squareNorm w := hp.trans_le horder
  have hg1 := gram_identity (combination v w c d) w
  have hg2 := gram_identity v (combination v w c d)
  rw [cramer_first] at hg1
  rw [cramer_second] at hg2
  have hc : c ^ 2 * area v w ^ 2 ≤ squareNorm (combination v w c d) * squareNorm w := by
    nlinarith [sq_nonneg (scalarProduct (combination v w c d) w)]
  have hd : d ^ 2 * area v w ^ 2 ≤ squareNorm v * squareNorm (combination v w c d) := by
    nlinarith [sq_nonneg (scalarProduct v (combination v w c d))]
  constructor
  · apply (mul_le_mul_iff_left₀ hq).mp
    calc
      _ = c ^ 2 * (3 * (squareNorm v * squareNorm w)) := by ring
      _ ≤ c ^ 2 * (4 * area v w ^ 2) := mul_le_mul_of_nonneg_left harea (sq_nonneg c)
      _ = 4 * (c ^ 2 * area v w ^ 2) := by ring
      _ ≤ 4 * (squareNorm (combination v w c d) * squareNorm w) := by linarith only [hc]
      _ = _ := by ring
  · apply (mul_le_mul_iff_left₀ hp).mp
    calc
      _ = d ^ 2 * (3 * (squareNorm v * squareNorm w)) := by ring
      _ ≤ d ^ 2 * (4 * area v w ^ 2) := mul_le_mul_of_nonneg_left harea (sq_nonneg d)
      _ = 4 * (d ^ 2 * area v w ^ 2) := by ring
      _ ≤ 4 * (squareNorm v * squareNorm (combination v w c d)) := by linarith only [hd]
      _ = _ := by ring

theorem box_energy (x : Fin 2 → ℝ) (R : ℝ) (hbox : ∀ i, |x i| ≤ R) : squareNorm x ≤ 2 * R ^ 2 := by
  have h0 := pow_le_pow_left₀ (abs_nonneg (x 0)) (hbox 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg (x 1)) (hbox 1) 2
  simp only [sq_abs] at h0 h1
  unfold squareNorm
  linarith

theorem bound_of_weighted_square (c P R : ℝ) (hp : 0 < P) (hR : 0 ≤ R)
    (hc : c ^ 2 * P ≤ 4 * R ^ 2) : |c| ≤ sideLength R P := by
  have hs : 0 < Real.sqrt P := Real.sqrt_pos.mpr hp
  apply (le_div_iff₀ hs).mpr
  have hsq : (|c| * Real.sqrt P) ^ 2 ≤ (2 * R) ^ 2 := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hp.le]
    nlinarith
  exact (sq_le_sq₀ (mul_nonneg (abs_nonneg c) hs.le) (by positivity)).mp hsq

theorem box_coordinate_bounds (v w : Fin 2 → ℝ) (c d R : ℝ) (hR : 0 ≤ R)
    (hp : 0 < squareNorm v) (horder : squareNorm v ≤ squareNorm w)
    (harea : 3 * (squareNorm v * squareNorm w) ≤ 4 * area v w ^ 2)
    (hbox : ∀ i, |combination v w c d i| ≤ R) :
    |c| ≤ sideLength R (squareNorm v) ∧ |d| ≤ sideLength R (squareNorm w) := by
  have hc := coordinate_square_bounds v w c d hp horder harea
  have he := box_energy _ R hbox
  exact ⟨bound_of_weighted_square c _ R hp hR (by nlinarith [sq_nonneg R]),
    bound_of_weighted_square d _ R (hp.trans_le horder) hR (by nlinarith [sq_nonneg R])⟩

theorem sideLength_order (R P Q : ℝ) (hR : 0 ≤ R) (hP : 0 < P) (hPQ : P ≤ Q) :
    sideLength R Q ≤ sideLength R P :=
  div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hP) (Real.sqrt_le_sqrt hPQ)

theorem sideLength_product (v w : Fin 2 → ℝ) (R : ℝ)
    (hp : 0 < squareNorm v) (horder : squareNorm v ≤ squareNorm w)
    (harea : 3 * (squareNorm v * squareNorm w) ≤ 4 * area v w ^ 2) :
    sideLength R (squareNorm v) * sideLength R (squareNorm w) ≤ 4 * R ^ 2 / |area v w| := by
  have hq : 0 < squareNorm w := hp.trans_le horder
  have hD : 0 < |area v w| := by
    apply abs_pos.mpr
    intro h
    rw [h] at harea
    have hprod := mul_pos hp hq
    nlinarith
  calc
    _ = 4 * R ^ 2 / (Real.sqrt (squareNorm v) * Real.sqrt (squareNorm w)) := by
      unfold sideLength
      rw [div_mul_div_comm]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD (area_length_bound v w)

theorem sideLength_inverse_bound (R P K : ℝ) (hR : 0 ≤ R) (hP : 0 < P) (hK : 0 ≤ K)
    (hKP : 1 ≤ K * P) : sideLength R P ≤ 2 * R * (K + 1) := by
  have hcoeff : K ≤ (K + 1) ^ 2 := by nlinarith [sq_nonneg K]
  have hprod : 1 ≤ (K + 1) ^ 2 * P := hKP.trans (mul_le_mul_of_nonneg_right hcoeff hP.le)
  have hs : 1 ≤ (K + 1) * Real.sqrt P := by
    apply (sq_le_sq₀ zero_le_one (mul_nonneg (by linarith) (Real.sqrt_nonneg P))).mp
    rw [one_pow, mul_pow, Real.sq_sqrt hP.le]
    exact hprod
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hP)).mpr
  have h := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * R by positivity)
  simpa only [mul_one, mul_assoc] using h

theorem sideLength_lower_square (R P Q D : ℝ) (hP : 0 < P) (hPQ : P ≤ Q)
    (harea : 3 * (P * Q) ≤ 4 * D ^ 2) : R ^ 2 ≤ sideLength R P ^ 2 * |D| := by
  have hpp : P ^ 2 ≤ P * Q := by nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hPQ)]
  have hpD : P ≤ 2 * |D| := by nlinarith [sq_abs D, abs_nonneg D]
  have hscale : sideLength R P ^ 2 * P = 4 * R ^ 2 := by
    unfold sideLength
    rw [div_pow, Real.sq_sqrt hP.le]
    field_simp
    ring
  apply (mul_le_mul_iff_left₀ hP).mp
  have hscaled := congrArg (fun x : ℝ ↦ x * |D|) hscale
  have hR := mul_le_mul_of_nonneg_left hpD (sq_nonneg R)
  have hRD := mul_nonneg (sq_nonneg R) (abs_nonneg D)
  nlinarith

end PaperP1.BinaryLatticeCoordinateBounds
