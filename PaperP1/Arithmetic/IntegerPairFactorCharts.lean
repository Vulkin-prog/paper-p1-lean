module

public import PaperP1.Arithmetic.IntegerFactorProjectiveCurve

/-! # Exact affine factor charts for arbitrary signed integer projective pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPairFactorCharts

open Finset PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
open PaperP1.BiquadraticCoefficientPolynomials PaperP1.BivariateEvaluation

theorem clear_power {R : Type*} [Field R] (x y : R) (hy : y ≠ 0) (a i : ℕ) (hi : i ≤ a) :
    y ^ a * (x / y) ^ i = x ^ i * y ^ (a - i) := by
  calc
    _ = x ^ i * (y ^ a * (y⁻¹) ^ i) := by rw [div_eq_mul_inv, mul_pow]; ring
    _ = _ := by rw [PaperP1.BivariateReciprocalProduct.reverse_power y hy a i hi]

theorem evaluation_sum (a b : ℕ) (w : Exponent a b → ℤ) (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (biform a b w) =
      ∑ i : Exponent a b, w i * x 0 ^ i.1.val * x 1 ^ (a - i.1.val) *
        y 0 ^ i.2.val * y 1 ^ (b - i.2.val) := by
  rw [biform_eval_original]
  unfold BidegreeOneElimination.original
  simp_rw [forms_eval, Finset.sum_mul]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem rectangle_evaluation_clearing (a b : ℕ) (w : Exponent a b → ℤ)
    (x y : Fin 2 → ℤ) (hx : x 1 ≠ 0) (hy : y 1 ≠ 0) :
    ((MvPolynomial.eval₂ (MvPolynomial.eval y) x (biform a b w) : ℤ) : ℚ) =
      (x 1 : ℚ) ^ a * (y 1 : ℚ) ^ b *
        evaluate ((x 0 : ℚ) / x 1) ((y 0 : ℚ) / y 1) (rectangle a b w) := by
  have hxQ : (x 1 : ℚ) ≠ 0 := by exact_mod_cast hx
  have hyQ : (y 1 : ℚ) ≠ 0 := by exact_mod_cast hy
  rw [evaluation_sum, rectangle_evaluation]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  have hi : i.1.val ≤ a := by have := i.1.isLt; omega
  have hj : i.2.val ≤ b := by have := i.2.isLt; omega
  calc
    _ = (w i : ℚ) * ((x 1 : ℚ) ^ a * ((x 0 : ℚ) / x 1) ^ i.1.val) *
        ((y 1 : ℚ) ^ b * ((y 0 : ℚ) / y 1) ^ i.2.val) := by
      rw [clear_power _ _ hxQ a i.1.val hi, clear_power _ _ hyQ b i.2.val hj]
      ring
    _ = _ := by ring

theorem rectangle_zero_iff (a b : ℕ) (w : Exponent a b → ℤ)
    (x y : Fin 2 → ℤ) (hx : x 1 ≠ 0) (hy : y 1 ≠ 0) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (biform a b w) = 0 ↔
      evaluate ((x 0 : ℚ) / x 1) ((y 0 : ℚ) / y 1) (rectangle a b w) = 0 := by
  have hc := rectangle_evaluation_clearing a b w x y hx hy
  have hxQ : (x 1 : ℚ) ≠ 0 := by exact_mod_cast hx
  have hyQ : (y 1 : ℚ) ≠ 0 := by exact_mod_cast hy
  have hd : (x 1 : ℚ) ^ a * (y 1 : ℚ) ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hxQ) (pow_ne_zero _ hyQ)
  constructor
  · intro hz
    rw [hz, Int.cast_zero] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left hd
  · intro hz
    rw [hz, mul_zero] at hc
    exact_mod_cast hc

theorem projective_zero_iff (F : Polynomial (Polynomial ℤ)) (x y : Fin 2 → ℤ)
    (hx : x 1 ≠ 0) (hy : y 1 ≠ 0) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (IntegerFactorProjectiveCurve.projective F) = 0 ↔
      evaluate ((x 0 : ℚ) / x 1) ((y 0 : ℚ) / y 1) F = 0 := by
  simpa only [IntegerFactorProjectiveCurve.projective, IntegerFactorProjectiveCurve.reconstruction] using
    rectangle_zero_iff _ _ (IntegerFactorProjectiveCurve.coefficients F) x y hx hy

end PaperP1.IntegerPairFactorCharts
