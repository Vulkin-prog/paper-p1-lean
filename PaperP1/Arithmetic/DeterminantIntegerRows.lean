module

public import PaperP1.Arithmetic.TwoKernelDeterminantBoxes
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FieldSimp

/-! # Actual rational monomial rows clear to bounded integer determinant rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantIntegerRows

open Finset PaperP1.TwoKernelDeterminantBoxes

abbrev Exponent (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

def integerEntry (A B : ℕ) (p : Quad) (i : Exponent A B) : ℤ :=
  ((p.1.1 ^ i.1.val * p.1.2 ^ (A - i.1.val) * p.2.2 ^ i.2.val * p.2.1 ^ (B - i.2.val) : ℕ) : ℤ)

def denominator (A B : ℕ) (p : Quad) : ℚ := (p.1.2 : ℚ) ^ A * (p.2.1 : ℚ) ^ B

def rationalEntry (A B : ℕ) (p : Quad) (i : Exponent A B) : ℚ :=
  ((p.1.1 : ℚ) / p.1.2) ^ i.1.val * ((p.2.2 : ℚ) / p.2.1) ^ i.2.val


def integerMatrix (A B : ℕ) (P : Exponent A B → Quad) : Matrix (Exponent A B) (Exponent A B) ℤ :=
  Matrix.of fun i j ↦ integerEntry A B (P i) j

def rationalMatrix (A B : ℕ) (P : Exponent A B → Quad) : Matrix (Exponent A B) (Exponent A B) ℚ :=
  Matrix.of fun i j ↦ rationalEntry A B (P i) j

theorem homogeneous_clearing {x y : ℚ} (hy : y ≠ 0) {A a : ℕ} (ha : a ≤ A) :
    y ^ A * (x / y) ^ a = x ^ a * y ^ (A - a) := by
  rw [div_pow, ← mul_div_assoc]
  apply (div_eq_iff (pow_ne_zero a hy)).mpr
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ha]
  ring

theorem entry_clearing (A B : ℕ) (p : Quad) (he : 0 < p.1.2) (hu : 0 < p.2.1)
    (i : Exponent A B) :
    denominator A B p * rationalEntry A B p i = (integerEntry A B p i : ℚ) := by
  have heq : (p.1.2 : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  have huq : (p.2.1 : ℚ) ≠ 0 := by exact_mod_cast hu.ne'
  unfold denominator rationalEntry integerEntry
  push_cast
  calc
    _ = ((p.1.2 : ℚ) ^ A * ((p.1.1 : ℚ) / p.1.2) ^ i.1.val) *
        ((p.2.1 : ℚ) ^ B * ((p.2.2 : ℚ) / p.2.1) ^ i.2.val) := by ring
    _ = _ := by
      rw [homogeneous_clearing heq (by have := i.1.isLt; omega),
        homogeneous_clearing huq (by have := i.2.isLt; omega)]
      ring

theorem denominator_pos (A B : ℕ) (p : Quad) (he : 0 < p.1.2) (hu : 0 < p.2.1) :
    0 < denominator A B p := by
  unfold denominator
  exact mul_pos (pow_pos (by exact_mod_cast he : (0 : ℚ) < p.1.2) _)
    (pow_pos (by exact_mod_cast hu : (0 : ℚ) < p.2.1) _)

theorem entry_height (A B X : ℕ) (p : Quad)
    (hd : p.1.1 ≤ X) (he : p.1.2 ≤ X) (hu : p.2.1 ≤ X) (hv : p.2.2 ≤ X)
    (i : Exponent A B) : (integerEntry A B p i).natAbs ≤ X ^ (A + B) := by
  unfold integerEntry
  rw [Int.natAbs_natCast]
  calc
    _ ≤ X ^ i.1.val * X ^ (A - i.1.val) * X ^ i.2.val * X ^ (B - i.2.val) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left he _))
        (Nat.pow_le_pow_left hv _)) (Nat.pow_le_pow_left hu _)
    _ = _ := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      have := i.1.isLt
      have := i.2.isLt
      omega

theorem determinant_clearing (A B : ℕ) (P : Exponent A B → Quad)
    (he : ∀ i, 0 < (P i).1.2) (hu : ∀ i, 0 < (P i).2.1) :
    ((integerMatrix A B P).det : ℚ) =
      (∏ i, denominator A B (P i)) * (rationalMatrix A B P).det := by
  rw [Int.cast_det]
  have hm : (integerMatrix A B P).map (fun z : ℤ ↦ (z : ℚ)) =
      Matrix.of (fun i j ↦ denominator A B (P i) * rationalMatrix A B P i j) := by
    ext i j
    exact (entry_clearing A B (P i) (he i) (hu i) j).symm
  rw [hm, Matrix.det_mul_column]

theorem integer_det_zero_of_small (A B : ℕ) (P : Exponent A B → Quad)
    (he : ∀ i, 0 < (P i).1.2) (hu : ∀ i, 0 < (P i).2.1)
    (hsmall : |(rationalMatrix A B P).det| *
      (∏ i, denominator A B (P i)) < 1) :
    (integerMatrix A B P).det = 0 := by
  have hp : (0 : ℚ) < ∏ i, denominator A B (P i) := prod_pos (fun i _ ↦ denominator_pos A B (P i) (he i) (hu i))
  have hh : |((integerMatrix A B P).det : ℚ)| < 1 := by
    rw [determinant_clearing A B P he hu, abs_mul, abs_of_pos hp]
    simpa only [mul_comm] using hsmall
  have hi : |(integerMatrix A B P).det| < (1 : ℤ) := by exact_mod_cast hh
  have hb := abs_lt.mp hi
  omega

theorem rational_det_zero_of_small (A B : ℕ) (P : Exponent A B → Quad)
    (he : ∀ i, 0 < (P i).1.2) (hu : ∀ i, 0 < (P i).2.1)
    (hsmall : |(rationalMatrix A B P).det| *
      (∏ i, denominator A B (P i)) < 1) :
    (rationalMatrix A B P).det = 0 := by
  have hh := determinant_clearing A B P he hu
  rw [integer_det_zero_of_small A B P he hu hsmall, Int.cast_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left
    ((prod_pos (fun i _ ↦ denominator_pos A B (P i) (he i) (hu i))).ne')

end PaperP1.DeterminantIntegerRows
