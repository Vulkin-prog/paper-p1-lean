module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic.LinearCombination

/-! # Actual polynomial functions and evaluations on a quadratic curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticPolynomialAlgebra

open Polynomial
open scoped QuadraticAlgebra

variable {F : Type*} [Field F]

abbrev CurveRing (f : F[X]) := QuadraticAlgebra F[X] f 0

def evaluation (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) : CurveRing f →+* F where
  toFun z := z.re.eval x + y * z.im.eval x
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by
    change (z + w).re.eval x + y * (z + w).im.eval x =
      (z.re.eval x + y * z.im.eval x) + (w.re.eval x + y * w.im.eval x)
    rw [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, eval_add, eval_add]
    ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, eval_add, eval_mul,
      zero_mul, add_zero]
    rw [← hy]
    ring

theorem evaluation_base (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) (P : F[X]) :
    evaluation f x y hy (algebraMap F[X] (CurveRing f) P) = P.eval x := by
  simp [evaluation]

theorem evaluation_root (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) :
    evaluation f x y hy QuadraticAlgebra.omega = y := by simp [evaluation]

theorem opposite_zero_iff (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x)
    (h2 : (2 : F) ≠ 0) (hyn : y ≠ 0) (z : CurveRing f) :
    evaluation f x y hy z = 0 ∧ evaluation f x (-y) (by simpa only [neg_sq] using hy) z = 0 ↔
      z.re.eval x = 0 ∧ z.im.eval x = 0 := by
  constructor
  · rintro ⟨hplus, hminus⟩
    change z.re.eval x + y * z.im.eval x = 0 at hplus
    change z.re.eval x + (-y) * z.im.eval x = 0 at hminus
    have hb : 2 * y * z.im.eval x = 0 := by linear_combination hplus - hminus
    have him := (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h2 hyn)
    exact ⟨by simpa only [him, mul_zero, add_zero] using hplus, him⟩
  · rintro ⟨hre, him⟩
    change (z.re.eval x + y * z.im.eval x = 0) ∧ (z.re.eval x + (-y) * z.im.eval x = 0)
    simp only [hre, him, mul_zero, add_zero, and_self]


@[simp]
theorem evaluation_apply (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x) (z : CurveRing f) :
    evaluation f x y hy z = z.re.eval x + y * z.im.eval x := rfl

theorem zero_iff (f : F[X]) (z : CurveRing f) : z = 0 ↔ z.re = 0 ∧ z.im = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hre, him⟩
    apply QuadraticAlgebra.ext <;> assumption

theorem base_power_mul_re (f P : F[X]) (m : ℕ) (z : CurveRing f) :
    ((algebraMap F[X] (CurveRing f) P) ^ m * z).re = P ^ m * z.re := by
  rw [← map_pow]
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero]

theorem base_power_mul_im (f P : F[X]) (m : ℕ) (z : CurveRing f) :
    ((algebraMap F[X] (CurveRing f) P) ^ m * z).im = P ^ m * z.im := by
  rw [← map_pow]
  simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, mul_zero, zero_mul, add_zero]

theorem norm_formula (f : F[X]) (z : CurveRing f) :
    QuadraticAlgebra.norm z = z.re ^ 2 - f * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem exists_nonzero_sign (f : F[X]) (x y : F) (hy : y ^ 2 = f.eval x)
    (h2 : (2 : F) ≠ 0) (hyn : y ≠ 0) (z : CurveRing f)
    (hne : z.re.eval x ≠ 0 ∨ z.im.eval x ≠ 0) :
    evaluation f x y hy z ≠ 0 ∨ evaluation f x (-y) (by simpa only [neg_sq] using hy) z ≠ 0 := by
  by_contra hnot
  have hh := not_or.mp hnot
  have hz := (opposite_zero_iff f x y hy h2 hyn z).mp ⟨not_not.mp hh.1, not_not.mp hh.2⟩
  rcases hne with ha | hb
  · exact ha hz.1
  · exact hb hz.2

end PaperP1.HyperellipticPolynomialAlgebra
