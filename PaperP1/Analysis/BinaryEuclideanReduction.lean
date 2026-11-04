module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.Order.Round
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Exact two-dimensional nearest-vector reduction and its area estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryEuclideanReduction

def squareNorm (v : Fin 2 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

def scalarProduct (v w : Fin 2 → ℝ) : ℝ := v 0 * w 0 + v 1 * w 1

def area (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

def multiple (v w : Fin 2 → ℝ) : ℤ := round (scalarProduct v w / squareNorm v)

def reduce (v w : Fin 2 → ℝ) : Fin 2 → ℝ := fun i ↦ w i - (multiple v w : ℝ) * v i

theorem squareNorm_nonnegative (v : Fin 2 → ℝ) : 0 ≤ squareNorm v := by
  unfold squareNorm
  positivity

theorem squareNorm_positive (v : Fin 2 → ℝ) (hv : v ≠ 0) : 0 < squareNorm v := by
  have hn := squareNorm_nonnegative v
  by_contra h
  have hz : squareNorm v = 0 := le_antisymm (by linarith) hn
  have h0 : v 0 = 0 := by unfold squareNorm at hz; nlinarith [sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by unfold squareNorm at hz; nlinarith [sq_nonneg (v 0)]
  apply hv
  funext i
  fin_cases i <;> assumption

theorem gram_identity (v w : Fin 2 → ℝ) :
    squareNorm v * squareNorm w = scalarProduct v w ^ 2 + area v w ^ 2 := by
  unfold squareNorm scalarProduct area
  ring

theorem reduced_scalar_product (v w : Fin 2 → ℝ) :
    scalarProduct v (reduce v w) = scalarProduct v w - (multiple v w : ℝ) * squareNorm v := by
  unfold scalarProduct reduce squareNorm
  ring

theorem reduced_area (v w : Fin 2 → ℝ) : area v (reduce v w) = area v w := by
  unfold area reduce
  ring

theorem reduced_projection_bound (v w : Fin 2 → ℝ) (hv : v ≠ 0) :
    |scalarProduct v (reduce v w)| ≤ squareNorm v / 2 := by
  have hp := squareNorm_positive v hv
  have hround := abs_sub_round (scalarProduct v w / squareNorm v)
  have hmul := mul_le_mul_of_nonneg_right hround hp.le
  calc
    _ = |(scalarProduct v w / squareNorm v - (multiple v w : ℝ)) * squareNorm v| := by
      rw [reduced_scalar_product]
      congr 1
      field_simp
    _ = |scalarProduct v w / squareNorm v - (multiple v w : ℝ)| * squareNorm v := by
      rw [abs_mul, abs_of_pos hp]
    _ ≤ (1 / 2 : ℝ) * squareNorm v := hmul
    _ = _ := by ring

theorem reduced_area_bound (v w : Fin 2 → ℝ) (hv : v ≠ 0)
    (hshort : squareNorm v ≤ squareNorm (reduce v w)) :
    3 * (squareNorm v * squareNorm (reduce v w)) ≤ 4 * area v w ^ 2 := by
  have hp := squareNorm_nonnegative v
  have hb := reduced_projection_bound v w hv
  have hbounds := abs_le.mp hb
  have hdot : 4 * scalarProduct v (reduce v w) ^ 2 ≤ squareNorm v ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hbounds.2) (show 0 ≤ squareNorm v / 2 + scalarProduct v (reduce v w) by linarith [hbounds.1])
    nlinarith
  have hnorm := mul_nonneg hp (sub_nonneg.mpr hshort)
  have hgram := gram_identity v (reduce v w)
  rw [reduced_area] at hgram
  nlinarith

end PaperP1.BinaryEuclideanReduction
