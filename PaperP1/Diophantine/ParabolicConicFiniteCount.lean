module

public import PaperP1.Arithmetic.SquareCongruenceRangeCount
public import PaperP1.Algebra.ConicNormCoordinates

/-! # A finite divisor bound for actual parabolic conic zeros

Only the first coordinate is bounded. The actual square coordinate is
injective on zeros when the leading coefficient and linear term are nonzero.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ParabolicConicFiniteCount

open Finset ConicNormCoordinates

theorem zero_square (Q : Coefficients) (hΔ : discriminant Q = 0) (z : ℤ × ℤ)
    (hz : value Q z.1 z.2 = 0) :
    squareCoordinate Q z ^ 2 = linear Q * z.1 + constant Q := by
  simpa only [hΔ, hz, zero_mul, mul_zero, zero_add, add_zero] using square_identity Q z

theorem square_coordinate_injective (Q : Coefficients) (hc : Q.c ≠ 0)
    (hΔ : discriminant Q = 0) (hβ : linear Q ≠ 0) :
    Set.InjOn (squareCoordinate Q) {z : ℤ × ℤ | value Q z.1 z.2 = 0} := by
  intro z hz w hw he
  have hzq := zero_square Q hΔ z hz
  have hwq := zero_square Q hΔ w hw
  have hx : z.1 = w.1 := mul_left_cancel₀ hβ (by rw [he] at hzq; linarith)
  change 2 * Q.c * z.2 + Q.b * z.1 + Q.e =
    2 * Q.c * w.2 + Q.b * w.1 + Q.e at he
  rw [hx] at he
  have hy : z.2 = w.2 :=
    mul_left_cancel₀ (mul_ne_zero (by decide : (2 : ℤ) ≠ 0) hc) (by linarith)
  exact Prod.ext hx hy

theorem finite_count (Q : Coefficients) (hc : Q.c ≠ 0)
    (hΔ : discriminant Q = 0) (hβ : linear Q ≠ 0) (H : ℕ) (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, value Q z.1 z.2 = 0 ∧ |z.1| ≤ (H : ℤ)) :
    (S.card : ℝ) ≤ 2 * ((linear Q).natAbs.divisors.card : ℝ) *
      (Real.sqrt (2 * (H : ℝ)) + 1) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [card_empty, Nat.cast_zero]
    positivity
  obtain ⟨base, hbase⟩ := hne
  let M := (linear Q).natAbs
  have hM : 0 < M := Int.natAbs_pos.mpr hβ
  have hMβ : (M : ℤ) ∣ linear Q := by
    change ((linear Q).natAbs : ℤ) ∣ _
    rw [Int.natCast_natAbs]
    exact abs_dvd_self _
  have hMr : (M : ℝ) = |(linear Q : ℝ)| := by
    simp only [M, Nat.cast_natAbs, Int.cast_abs]
  have hdifference (z w : ℤ × ℤ) (hz : z ∈ S) (hw : w ∈ S) :
      squareCoordinate Q z ^ 2 - squareCoordinate Q w ^ 2 = linear Q * (z.1 - w.1) := by
    rw [zero_square Q hΔ z (hS z hz).1, zero_square Q hΔ w (hS w hw).1]
    ring
  have hbound := SquareCongruenceRangeCount.signed_count M hM (squareCoordinate Q base)
    (2 * (H : ℝ)) (by positivity) (S.image (squareCoordinate Q)) (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
      rw [hdifference z base hz hbase]
      exact dvd_mul_of_dvd_left hMβ _) (by
      intro v hv u hu
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hv
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hu
      have he : (squareCoordinate Q z : ℝ) ^ 2 - (squareCoordinate Q w : ℝ) ^ 2 =
          (linear Q : ℝ) * ((z.1 : ℝ) - w.1) := by exact_mod_cast hdifference z w hz hw
      have hzx : |(z.1 : ℝ)| ≤ H := by exact_mod_cast (hS z hz).2
      have hwx : |(w.1 : ℝ)| ≤ H := by exact_mod_cast (hS w hw).2
      have hdiff : |(z.1 : ℝ) - w.1| ≤ 2 * H := by
        have hh := abs_sub (z.1 : ℝ) (w.1 : ℝ)
        linarith
      calc
        _ = (linear Q : ℝ) * ((z.1 : ℝ) - w.1) := he
        _ ≤ |(linear Q : ℝ) * ((z.1 : ℝ) - w.1)| := le_abs_self _
        _ = |(linear Q : ℝ)| * |(z.1 : ℝ) - w.1| := abs_mul _ _
        _ ≤ _ := by rw [hMr]; exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))
  have hinj : Set.InjOn (squareCoordinate Q) (S : Set (ℤ × ℤ)) := by
    intro z hz w hw he
    exact square_coordinate_injective Q hc hΔ hβ (hS z hz).1 (hS w hw).1 he
  simpa only [card_image_of_injOn hinj] using hbound

end PaperP1.ParabolicConicFiniteCount
