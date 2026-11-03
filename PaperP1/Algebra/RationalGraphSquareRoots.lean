module

public import PaperP1.Algebra.OffsetCommonQuotientGraph
public import PaperP1.Algebra.SquareInFractionField
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Simple selected roots of actual rational-graph squares give the required offset matches -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalGraphSquareRoots

open Polynomial Finset PaperP1.FormalWordPolynomials

variable {F : Type*} [Field F]

def value (c j : F) (P p q : F[X]) : FractionRing F[X] :=
  algebraMap F[X] (FractionRing F[X]) (C c * P) *
    (algebraMap F[X] (FractionRing F[X]) p / algebraMap F[X] (FractionRing F[X]) q +
      algebraMap F[X] (FractionRing F[X]) (C j))

theorem cleared_square (c j : F) (P p q : F[X]) (hq : q ≠ 0) (hsq : IsSquare (value c j P p q)) :
    IsSquare (C c * P * (p + C j * q) * q) := by
  let φ := algebraMap F[X] (FractionRing F[X])
  have hqmap : φ q ≠ 0 := by
    intro hz
    exact hq (IsFractionRing.injective F[X] (FractionRing F[X]) (by simpa only [map_zero] using hz))
  have heq : φ (C c * P * (p + C j * q) * q) = value c j P p q * (φ q) ^ 2 := by
    simp only [value, map_mul, map_add]
    change φ (C c) * φ P * (φ p + φ (C j) * φ q) * φ q =
      (φ (C c) * φ P * (φ p / φ q + φ (C j))) * (φ q) ^ 2
    field_simp
  apply (SquareInFractionField.square_reflect (K := FractionRing F[X]) _).mp
  rw [heq]
  exact hsq.mul ⟨φ q, pow_two _⟩

theorem square_derivative_zero (P : F[X]) (hsq : IsSquare P) (z : F) (hz : P.eval z = 0) :
    P.derivative.eval z = 0 := by
  obtain ⟨r, rfl⟩ := hsq
  have hr : r.eval z = 0 := mul_self_eq_zero.mp (by simpa only [eval_mul] using hz)
  simp only [derivative_mul, eval_add, eval_mul, hr, mul_zero, zero_mul, add_zero]

theorem root_match (c j : F) (P p q : F[X]) (hq : q ≠ 0) (hc : c ≠ 0)
    (hsq : IsSquare (value c j P p q)) (z : F)
    (hP : P.eval z = 0) (hderiv : P.derivative.eval z ≠ 0) (hqeval : q.eval z ≠ 0) :
    p.eval z = -j * q.eval z := by
  have hcleared := cleared_square c j P p q hq hsq
  have hzero : (C c * P * (p + C j * q) * q).eval z = 0 := by
    simp only [eval_mul, eval_C, hP, mul_zero, zero_mul]
  have hd := square_derivative_zero _ hcleared z hzero
  simp only [derivative_mul, derivative_C, eval_add, eval_mul, eval_C, hP,
    mul_zero, zero_mul, zero_add, add_zero] at hd
  have hroot : p.eval z + j * q.eval z = 0 := by
    simpa only [mul_eq_zero, hc, hderiv, hqeval, false_or, or_false] using hd
  linear_combination hroot

variable [CharZero F]

theorem selected_derivative_ne_zero (I : Finset ℤ) (i : ℤ) (hi : i ∈ I) :
    (linearOver F I).derivative.eval (-(i : F)) ≠ 0 := by
  have hfactor : linearOver F I = (X + C (i : F)) * linearOver F (I.erase i) :=
    (Finset.mul_prod_erase I (fun j : ℤ ↦ (X : F[X]) + C (j : F)) hi).symm
  have hrest : (linearOver F (I.erase i)).eval (-(i : F)) ≠ 0 := by
    rw [linearOver, eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    simp only [eval_add, eval_X, eval_C]
    intro hz
    have heq : (j : F) = (i : F) := by linear_combination hz
    exact (mem_erase.mp hj).1 (Int.cast_injective heq)
  rw [hfactor, derivative_mul]
  simpa only [derivative_add, derivative_X, derivative_C, add_zero, eval_add, eval_mul,
    eval_one, eval_X, eval_C, neg_add_cancel, zero_mul, add_zero, one_mul] using hrest

theorem offset_match (c j : F) (I : Finset ℤ) (p q : F[X]) (hq : q ≠ 0) (hc : c ≠ 0)
    (hsq : IsSquare (value c j (linearOver F I) p q)) (i : ℤ) (hi : i ∈ I)
    (hqeval : q.eval (-(i : F)) ≠ 0) : p.eval (-(i : F)) = -j * q.eval (-(i : F)) := by
  have hroot : (linearOver F I).eval (-(i : F)) = 0 := by
    simp only [linearOver, eval_prod]
    exact Finset.prod_eq_zero_iff.mpr ⟨i, hi, by simp⟩
  exact root_match c j _ p q hq hc hsq _ hroot (selected_derivative_ne_zero I i hi) hqeval

end PaperP1.RationalGraphSquareRoots
