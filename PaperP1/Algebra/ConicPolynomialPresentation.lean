module

public import PaperP1.Algebra.ConicNormCoordinates

/-! # Actual polynomial presentations and norm images of every conic grid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConicPolynomialPresentation

open Polynomial Finset PaperP1.ConicNormCoordinates

def polynomial (Q : Coefficients) : ℤ[X][X] :=
  Polynomial.monomial 0 (Polynomial.monomial 0 Q.f + Polynomial.monomial 1 Q.d + Polynomial.monomial 2 Q.a) +
    Polynomial.monomial 1 (Polynomial.monomial 0 Q.e + Polynomial.monomial 1 Q.b) +
      Polynomial.monomial 2 (Polynomial.monomial 0 Q.c)

def coefficients (P : ℤ[X][X]) : Coefficients :=
  ⟨(P.coeff 0).coeff 2, (P.coeff 1).coeff 1, (P.coeff 2).coeff 0,
    (P.coeff 0).coeff 1, (P.coeff 1).coeff 0, (P.coeff 0).coeff 0⟩

theorem evaluation (Q : Coefficients) (x y : ℤ) :
    (polynomial Q).evalEval x y = value Q x y := by
  simp [polynomial, Polynomial.evalEval, value]
  ring

theorem reconstruction (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2) :
    polynomial (coefficients P) = P := by
  have hrow (y : ℕ) : (P.coeff y).natDegree ≤ 2 - y := by
    by_cases hy : P.coeff y = 0
    · simp only [hy, Polynomial.natDegree_zero, Nat.zero_le]
    · have hh := BivariateResultantDegree.coefficient_row_degree P y hy
      omega
  have hout : P.natDegree < 3 := by
    have hh := BivariateResultantDegree.outer_degree_le P
    omega
  have hexp : P = Polynomial.monomial 0 (P.coeff 0) + Polynomial.monomial 1 (P.coeff 1) +
      Polynomial.monomial 2 (P.coeff 2) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using Polynomial.as_sum_range' P 3 hout
  have h0 : P.coeff 0 = Polynomial.monomial 0 ((P.coeff 0).coeff 0) +
      Polynomial.monomial 1 ((P.coeff 0).coeff 1) + Polynomial.monomial 2 ((P.coeff 0).coeff 2) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
      Polynomial.as_sum_range' (P.coeff 0) 3 (by have hh := hrow 0; omega)
  have h1 : P.coeff 1 = Polynomial.monomial 0 ((P.coeff 1).coeff 0) +
      Polynomial.monomial 1 ((P.coeff 1).coeff 1) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
      Polynomial.as_sum_range' (P.coeff 1) 2 (by have hh := hrow 1; omega)
  have h2 : P.coeff 2 = Polynomial.monomial 0 ((P.coeff 2).coeff 0) := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using
      Polynomial.as_sum_range' (P.coeff 2) 1 (by have hh := hrow 2; omega)
  symm
  conv_lhs => rw [hexp, h0, h1, h2]
  rfl

theorem height_coefficients (P : ℤ[X][X]) :
    height (coefficients P) ≤ 6 * BivariateHeight.height P := by
  have h02 := BivariateHeight.coefficient_natAbs_le_height P 0 2
  have h11 := BivariateHeight.coefficient_natAbs_le_height P 1 1
  have h20 := BivariateHeight.coefficient_natAbs_le_height P 2 0
  have h01 := BivariateHeight.coefficient_natAbs_le_height P 0 1
  have h10 := BivariateHeight.coefficient_natAbs_le_height P 1 0
  have h00 := BivariateHeight.coefficient_natAbs_le_height P 0 0
  dsimp only [height, coefficients]
  omega

theorem outer_coefficient_ne_zero (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2)
    (hout : P.natDegree = 2) : (coefficients P).c ≠ 0 := by
  have hne : P ≠ 0 := by intro hz; simp only [hz, Polynomial.natDegree_zero] at hout; omega
  have hrow : P.coeff 2 ≠ 0 := by
    rw [← hout, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne
  have hh := BivariateResultantDegree.coefficient_row_degree P 2 hrow
  have hdeg : (P.coeff 2).natDegree = 0 := by omega
  have he := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  intro hc
  change (P.coeff 2).coeff 0 = 0 at hc
  apply hrow
  simpa only [hc, map_zero] using he

theorem norm_grid (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2) (B : ℕ)
    (z : ℤ × ℤ) (hz : z ∈ PlaneCurvePointCount.grid P B) :
    (transform (coefficients P) z).1 ^ 2 - discriminant (coefficients P) *
        (transform (coefficients P) z).2 ^ 2 = normConstant (coefficients P) ∧
      (transform (coefficients P) z).1.natAbs ≤ (10 * B + 6) * (6 * BivariateHeight.height P) ^ 2 ∧
        (transform (coefficients P) z).2.natAbs ≤ (6 * B + 2) * (6 * BivariateHeight.height P) := by
  have hh := (PlaneCurvePointCount.mem_grid P B z).mp hz
  have hx : z.1.natAbs ≤ B := by
    have hc : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
    exact_mod_cast hc
  have hy : z.2.natAbs ≤ B := by
    have hc : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
    exact_mod_cast hc
  have hzero : value (coefficients P) z.1 z.2 = 0 := by
    rw [← evaluation, reconstruction P hD]
    exact hh.2.2
  obtain ⟨hu, hv⟩ := transform_bounds (coefficients P) B z hx hy
  exact ⟨zero_maps_to_norm _ z hzero,
    hu.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (height_coefficients P) 2)),
    hv.trans (Nat.mul_le_mul_left _ (height_coefficients P))⟩

theorem grid_image_card (P : ℤ[X][X]) (B : ℕ) (hc : (coefficients P).c ≠ 0)
    (hΔ : discriminant (coefficients P) ≠ 0) :
    ((PlaneCurvePointCount.grid P B).image (transform (coefficients P))).card =
      (PlaneCurvePointCount.grid P B).card :=
  Finset.card_image_of_injective _ (transform_injective (coefficients P) hc hΔ)

end PaperP1.ConicPolynomialPresentation
