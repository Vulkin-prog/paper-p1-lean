module

public import PaperP1.Algebra.ConicPolynomialPresentation
public import PaperP1.Algebra.IntegerPlaneShear
public import Mathlib.Tactic.GCongr

/-! # Exact conic invariants and coefficient heights under integer shears -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConicCoordinateChanges

open Polynomial PaperP1.ConicNormCoordinates PaperP1.ConicPolynomialPresentation

def shearCoefficients (t : ℤ) (Q : Coefficients) : Coefficients :=
  ⟨Q.a, 2 * Q.a * t + Q.b, Q.a * t ^ 2 + Q.b * t + Q.c,
    Q.d, Q.d * t + Q.e, Q.f⟩

def determinant (Q : Coefficients) : ℤ :=
  Q.a * Q.e ^ 2 + Q.c * Q.d ^ 2 + Q.b ^ 2 * Q.f - Q.b * Q.d * Q.e - 4 * Q.a * Q.c * Q.f

theorem polynomial_expression (Q : Coefficients) :
    polynomial Q = C (C Q.a) * C X ^ 2 + C (C Q.b) * C X * X + C (C Q.c) * X ^ 2 +
      C (C Q.d) * C X + C (C Q.e) * X + C (C Q.f) := by
  simp only [polynomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_add, map_mul, map_pow,
    pow_zero, pow_one, mul_one]
  ring

theorem coefficients_polynomial (Q : Coefficients) : coefficients (polynomial Q) = Q := by
  cases Q
  norm_num only [coefficients, polynomial, Polynomial.coeff_add, Polynomial.coeff_monomial,
    Polynomial.coeff_zero, ite_true, ite_false, zero_add, add_zero]

theorem polynomial_shear (t : ℤ) (Q : Coefficients) :
    BivariateLinearShear.shear t (polynomial Q) = polynomial (shearCoefficients t Q) := by
  rw [polynomial_expression Q, polynomial_expression (shearCoefficients t Q)]
  simp only [map_add, map_mul, map_pow, IntegerPlaneShear.scalar,
    IntegerPlaneShear.inner_variable, IntegerPlaneShear.outer_variable]
  simp only [shearCoefficients, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem coefficients_shear (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2) (t : ℤ) :
    coefficients (BivariateLinearShear.shear t P) = shearCoefficients t (coefficients P) := by
  conv_lhs => rw [← reconstruction P hD, polynomial_shear, coefficients_polynomial]

theorem discriminant_shearCoefficients (t : ℤ) (Q : Coefficients) :
    discriminant (shearCoefficients t Q) = discriminant Q := by
  simp only [discriminant, shearCoefficients]
  ring

theorem normConstant_determinant (Q : Coefficients) : normConstant Q = 16 * Q.c * determinant Q := by
  simp only [normConstant, linear, discriminant, constant, determinant]
  ring

theorem determinant_shearCoefficients (t : ℤ) (Q : Coefficients) :
    determinant (shearCoefficients t Q) = determinant Q := by
  simp only [determinant, shearCoefficients]
  ring

theorem discriminant_shear (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2) (t : ℤ) :
    discriminant (coefficients (BivariateLinearShear.shear t P)) = discriminant (coefficients P) := by
  rw [coefficients_shear P hD t, discriminant_shearCoefficients]

theorem determinant_shear (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2) (t : ℤ) :
    determinant (coefficients (BivariateLinearShear.shear t P)) = determinant (coefficients P) := by
  rw [coefficients_shear P hD t, determinant_shearCoefficients]

theorem height_shear (t : ℕ) (ht : t ≤ 2) (Q : Coefficients) :
    height (shearCoefficients (t : ℤ) Q) ≤ 9 * height Q := by
  have hb := Int.natAbs_add_le (2 * Q.a * (t : ℤ)) Q.b
  have hc := Int.natAbs_add_le (Q.a * (t : ℤ) ^ 2 + Q.b * (t : ℤ)) Q.c
  have hc' := Int.natAbs_add_le (Q.a * (t : ℤ) ^ 2) (Q.b * (t : ℤ))
  have he := Int.natAbs_add_le (Q.d * (t : ℤ)) Q.e
  norm_num only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hb hc hc' he
  have hat := Nat.mul_le_mul_left (2 * Q.a.natAbs) ht
  have hat2 := Nat.mul_le_mul_left Q.a.natAbs (Nat.pow_le_pow_left ht 2)
  have hbt := Nat.mul_le_mul_left Q.b.natAbs ht
  have hdt := Nat.mul_le_mul_left Q.d.natAbs ht
  have hbb : (2 * Q.a * (t : ℤ) + Q.b).natAbs ≤ 4 * Q.a.natAbs + Q.b.natAbs := by
    calc
      _ ≤ 2 * Q.a.natAbs * t + Q.b.natAbs := hb
      _ ≤ 2 * Q.a.natAbs * 2 + Q.b.natAbs := Nat.add_le_add hat le_rfl
      _ = _ := by ring
  have hcc : (Q.a * (t : ℤ) ^ 2 + Q.b * (t : ℤ) + Q.c).natAbs ≤
      4 * Q.a.natAbs + 2 * Q.b.natAbs + Q.c.natAbs := by
    calc
      _ ≤ (Q.a * (t : ℤ) ^ 2 + Q.b * (t : ℤ)).natAbs + Q.c.natAbs := hc
      _ ≤ (Q.a.natAbs * t ^ 2 + Q.b.natAbs * t) + Q.c.natAbs := Nat.add_le_add hc' le_rfl
      _ ≤ (Q.a.natAbs * 2 ^ 2 + Q.b.natAbs * 2) + Q.c.natAbs :=
        Nat.add_le_add (Nat.add_le_add hat2 hbt) le_rfl
      _ = _ := by ring
  have hee : (Q.d * (t : ℤ) + Q.e).natAbs ≤ 2 * Q.d.natAbs + Q.e.natAbs := by
    calc
      _ ≤ Q.d.natAbs * t + Q.e.natAbs := he
      _ ≤ Q.d.natAbs * 2 + Q.e.natAbs := Nat.add_le_add hdt le_rfl
      _ = _ := by ring
  calc
    height (shearCoefficients (t : ℤ) Q) ≤ Q.a.natAbs + (4 * Q.a.natAbs + Q.b.natAbs) +
        (4 * Q.a.natAbs + 2 * Q.b.natAbs + Q.c.natAbs) + Q.d.natAbs +
          (2 * Q.d.natAbs + Q.e.natAbs) + Q.f.natAbs := by
      dsimp only [height, shearCoefficients]
      gcongr
    _ ≤ 9 * height Q := by
      dsimp only [height]
      nlinarith only [Nat.zero_le Q.a.natAbs, Nat.zero_le Q.b.natAbs, Nat.zero_le Q.c.natAbs,
        Nat.zero_le Q.d.natAbs, Nat.zero_le Q.e.natAbs, Nat.zero_le Q.f.natAbs]

end PaperP1.ConicCoordinateChanges
