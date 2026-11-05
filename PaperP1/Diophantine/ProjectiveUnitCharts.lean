module

public import PaperP1.Diophantine.LinearProjectiveFactor
public import PaperP1.Arithmetic.IntegerPairFactorCharts

/-! # Exact projective normalization over arbitrary commutative rings with unit denominators -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveUnitCharts

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.IntegerFactorProjectiveCurve
  PaperP1.HomogeneousCharts

variable {R : Type*} [CommRing R]

theorem clear_unit_power (u : R) (v : Rˣ) (a i : ℕ) (hi : i ≤ a) :
    (u * (↑v⁻¹ : R)) ^ i * (v : R) ^ a = u ^ i * (v : R) ^ (a - i) := by
  have hp : (v : R) ^ a = (v : R) ^ i * (v : R) ^ (a - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [mul_pow, hp]
  calc
    _ = u ^ i * (((↑v⁻¹ : R) * (v : R)) ^ i) * (v : R) ^ (a - i) := by
      rw [mul_pow]
      ring
    _ = _ := by simp

theorem binary_evaluation {A : Type*} [CommRing A] (F : MvPolynomial (Fin 2) A)
    (d : ℕ) (hF : F.IsHomogeneous d) (f : A →+* R) (z : Fin 2 → R) :
    MvPolynomial.eval₂ f z F =
      ∑ j : Fin (d + 1), f ((chart F).coeff j.val) * z 0 ^ j.val * z 1 ^ (d - j.val) := by
  conv_lhs => rw [PaperP1.BihomogeneousSwap.binary_expansion F hF]
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]

def value (G : ℤ[X][X]) (x y : Fin 2 → R) : R :=
  MvPolynomial.eval₂ (MvPolynomial.eval₂Hom (Int.castRingHom R) y) x (projective G)

theorem evaluation_sum (G : ℤ[X][X]) (x y : Fin 2 → R) :
    value G x y = ∑ i : PaperP1.DeterminantIntegerRows.Exponent (degreeX G) (degreeY G),
      ((G.coeff i.2.val).coeff i.1.val : R) * x 0 ^ i.1.val * x 1 ^ (degreeX G - i.1.val) *
        y 0 ^ i.2.val * y 1 ^ (degreeY G - i.2.val) := by
  rw [value, binary_evaluation _ _ (projective_homogeneous G)]
  simp_rw [PaperP1.LinearProjectiveFactor.projective_chart_coefficient]
  simp_rw [MvPolynomial.coe_eval₂Hom,
    binary_evaluation _ _ (Polynomial.isHomogeneous_homogenize _)]
  have hd (i : Fin (degreeX G + 1)) : ((Bivariate.swap G).coeff i.val).natDegree ≤ degreeY G := by
    simpa only [degreeX, degreeY, Bivariate.swap_swap_apply] using
      natDegree_coeff_le_degreeX (Bivariate.swap G) i.val
  simp_rw [chart, Polynomial.aeval_homogenize_X_one _ (hd _)]
  simp only [Int.coe_castRingHom, Finset.sum_mul, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _hi
  apply sum_congr rfl
  intro j _hj
  rw [PaperP1.BivariateDegrees.coeff_swap]
  ring

theorem evaluation_units (G : ℤ[X][X]) (u v : R) (X Y : Rˣ) :
    value G ![u, (X : R)] ![v, (Y : R)] =
      PaperP1.BivariateEvaluation.evaluate (u * (↑X⁻¹ : R)) (v * (↑Y⁻¹ : R)) G *
        (X : R) ^ degreeX G * (Y : R) ^ degreeY G := by
  have hev := PaperP1.BivariateEvaluation.rectangle_evaluation
    (u * (↑X⁻¹ : R)) (v * (↑Y⁻¹ : R)) (degreeX G) (degreeY G) (coefficients G)
  rw [reconstruction G] at hev
  rw [evaluation_sum, hev]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, coefficients]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply sum_congr rfl
  intro i _hi
  have hi : i.1.val ≤ degreeX G := by have := i.1.isLt; omega
  have hj : i.2.val ≤ degreeY G := by have := i.2.isLt; omega
  have hx := clear_unit_power u X (degreeX G) i.1.val hi
  have hy := clear_unit_power v Y (degreeY G) i.2.val hj
  calc
    _ = ((G.coeff i.2.val).coeff i.1.val : R) *
        ((u * (↑X⁻¹ : R)) ^ i.1.val * (X : R) ^ degreeX G) *
        ((v * (↑Y⁻¹ : R)) ^ i.2.val * (Y : R) ^ degreeY G) := by rw [hx, hy]; ring
    _ = _ := by ring

theorem integer_cast (G : ℤ[X][X]) (x y : Fin 2 → ℤ) :
    value G (fun i ↦ (x i : R)) (fun i ↦ (y i : R)) =
      ((MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) : ℤ) : R) := by
  rw [evaluation_sum, projective, PaperP1.IntegerPairFactorCharts.evaluation_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, coefficients]

theorem zero_iff (G : ℤ[X][X]) (u v : R) (X Y : Rˣ) :
    value G ![u, (X : R)] ![v, (Y : R)] = 0 ↔
      PaperP1.BivariateEvaluation.evaluate (u * (↑X⁻¹ : R)) (v * (↑Y⁻¹ : R)) G = 0 := by
  rw [evaluation_units, mul_assoc]
  exact ((X.isUnit.pow (degreeX G)).mul (Y.isUnit.pow (degreeY G))).mul_left_eq_zero

end PaperP1.ProjectiveUnitCharts
