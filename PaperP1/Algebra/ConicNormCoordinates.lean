module

public import PaperP1.Algebra.TotalDegreeMonomials
public import Mathlib.Tactic.Linarith

/-! # Exact norm coordinates and polynomial height budgets for an integer conic

The norm coefficient may have either sign. This module supplies algebra and
height transport, not a conic counting theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConicNormCoordinates

structure Coefficients where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ

def value (Q : Coefficients) (x y : ℤ) : ℤ :=
  Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2 + Q.d * x + Q.e * y + Q.f

def height (Q : Coefficients) : ℕ :=
  Q.a.natAbs + Q.b.natAbs + Q.c.natAbs + Q.d.natAbs + Q.e.natAbs + Q.f.natAbs

def discriminant (Q : Coefficients) : ℤ := Q.b ^ 2 - 4 * Q.a * Q.c

def linear (Q : Coefficients) : ℤ := 2 * Q.b * Q.e - 4 * Q.c * Q.d

def constant (Q : Coefficients) : ℤ := Q.e ^ 2 - 4 * Q.c * Q.f

def normConstant (Q : Coefficients) : ℤ := linear Q ^ 2 - 4 * discriminant Q * constant Q

def squareCoordinate (Q : Coefficients) (z : ℤ × ℤ) : ℤ :=
  2 * Q.c * z.2 + Q.b * z.1 + Q.e

def transform (Q : Coefficients) (z : ℤ × ℤ) : ℤ × ℤ :=
  (2 * discriminant Q * z.1 + linear Q, 2 * squareCoordinate Q z)

theorem coefficient_bounds (Q : Coefficients) :
    Q.a.natAbs ≤ height Q ∧ Q.b.natAbs ≤ height Q ∧ Q.c.natAbs ≤ height Q ∧
      Q.d.natAbs ≤ height Q ∧ Q.e.natAbs ≤ height Q ∧ Q.f.natAbs ≤ height Q := by
  dsimp only [height]
  omega

theorem square_identity (Q : Coefficients) (z : ℤ × ℤ) :
    squareCoordinate Q z ^ 2 = discriminant Q * z.1 ^ 2 + linear Q * z.1 + constant Q +
      4 * Q.c * value Q z.1 z.2 := by
  simp only [squareCoordinate, discriminant, linear, constant, value]
  ring

theorem norm_identity (Q : Coefficients) (z : ℤ × ℤ) :
    (transform Q z).1 ^ 2 - discriminant Q * (transform Q z).2 ^ 2 =
      normConstant Q - 16 * Q.c * discriminant Q * value Q z.1 z.2 := by
  simp only [transform, squareCoordinate, discriminant, linear, constant, normConstant, value]
  ring

theorem zero_maps_to_norm (Q : Coefficients) (z : ℤ × ℤ) (hz : value Q z.1 z.2 = 0) :
    (transform Q z).1 ^ 2 - discriminant Q * (transform Q z).2 ^ 2 = normConstant Q := by
  rw [norm_identity, hz, mul_zero, sub_zero]

theorem transform_injective (Q : Coefficients) (hc : Q.c ≠ 0) (hΔ : discriminant Q ≠ 0) :
    Function.Injective (transform Q) := by
  intro z w he
  have hx := congrArg (fun q : ℤ × ℤ ↦ q.1) he
  have hy := congrArg (fun q : ℤ × ℤ ↦ q.2) he
  change 2 * discriminant Q * z.1 + linear Q = 2 * discriminant Q * w.1 + linear Q at hx
  have hxx : z.1 = w.1 :=
    mul_left_cancel₀ (mul_ne_zero (by decide : (2 : ℤ) ≠ 0) hΔ) (by linarith)
  change 2 * (2 * Q.c * z.2 + Q.b * z.1 + Q.e) =
    2 * (2 * Q.c * w.2 + Q.b * w.1 + Q.e) at hy
  rw [hxx] at hy
  have hyy : z.2 = w.2 :=
    mul_left_cancel₀ (mul_ne_zero (by decide : (4 : ℤ) ≠ 0) hc) (by nlinarith [hy])
  exact Prod.ext hxx hyy

theorem discriminant_bound (Q : Coefficients) : (discriminant Q).natAbs ≤ 5 * height Q ^ 2 := by
  obtain ⟨ha, hb, hc, _hd, _he, _hf⟩ := coefficient_bounds Q
  have hsq := Nat.pow_le_pow_left hb 2
  have hmul := Nat.mul_le_mul ha hc
  have hh := Int.natAbs_sub_le (Q.b ^ 2) (4 * Q.a * Q.c)
  norm_num only [Int.natAbs_pow, Int.natAbs_mul] at hh
  dsimp only [discriminant]
  nlinarith

theorem linear_bound (Q : Coefficients) : (linear Q).natAbs ≤ 6 * height Q ^ 2 := by
  obtain ⟨_ha, hb, hc, hd, he, _hf⟩ := coefficient_bounds Q
  have hbe := Nat.mul_le_mul hb he
  have hcd := Nat.mul_le_mul hc hd
  have hh := Int.natAbs_sub_le (2 * Q.b * Q.e) (4 * Q.c * Q.d)
  norm_num only [Int.natAbs_mul] at hh
  dsimp only [linear]
  nlinarith

theorem constant_bound (Q : Coefficients) : (constant Q).natAbs ≤ 5 * height Q ^ 2 := by
  obtain ⟨_ha, _hb, hc, _hd, he, hf⟩ := coefficient_bounds Q
  have hsq := Nat.pow_le_pow_left he 2
  have hmul := Nat.mul_le_mul hc hf
  have hh := Int.natAbs_sub_le (Q.e ^ 2) (4 * Q.c * Q.f)
  norm_num only [Int.natAbs_pow, Int.natAbs_mul] at hh
  dsimp only [constant]
  nlinarith

theorem normConstant_bound (Q : Coefficients) :
    (normConstant Q).natAbs ≤ 136 * height Q ^ 4 := by
  have hsq := Nat.pow_le_pow_left (linear_bound Q) 2
  have hmul := Nat.mul_le_mul (discriminant_bound Q) (constant_bound Q)
  have hh := Int.natAbs_sub_le (linear Q ^ 2) (4 * discriminant Q * constant Q)
  norm_num only [Int.natAbs_pow, Int.natAbs_mul] at hh
  dsimp only [normConstant]
  nlinarith

theorem transform_bounds (Q : Coefficients) (H : ℕ) (z : ℤ × ℤ)
    (hx : z.1.natAbs ≤ H) (hy : z.2.natAbs ≤ H) :
    (transform Q z).1.natAbs ≤ (10 * H + 6) * height Q ^ 2 ∧
      (transform Q z).2.natAbs ≤ (6 * H + 2) * height Q := by
  obtain ⟨_ha, hb, hc, _hd, he, _hf⟩ := coefficient_bounds Q
  have hdx := Nat.mul_le_mul (discriminant_bound Q) hx
  have hcy := Nat.mul_le_mul hc hy
  have hbx := Nat.mul_le_mul hb hx
  have hu := Int.natAbs_add_le (2 * discriminant Q * z.1) (linear Q)
  have hv := Int.natAbs_add_le (2 * Q.c * z.2 + Q.b * z.1) Q.e
  have hv' := Int.natAbs_add_le (2 * Q.c * z.2) (Q.b * z.1)
  norm_num only [Int.natAbs_mul] at hu hv hv'
  constructor
  · change (2 * discriminant Q * z.1 + linear Q).natAbs ≤ _
    nlinarith [linear_bound Q]
  · change (2 * (2 * Q.c * z.2 + Q.b * z.1 + Q.e)).natAbs ≤ _
    rw [Int.natAbs_mul]
    norm_num
    nlinarith

end PaperP1.ConicNormCoordinates
