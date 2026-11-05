module

public import PaperP1.Diophantine.ProjectivePrimeExceptions
public import PaperP1.Diophantine.PrimitiveHomogeneousRootBound
public import PaperP1.Algebra.PolynomialHeightArithmetic

/-! # Explicit height bounds for the actual denominator-and-derivative integer -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectivePrimeHeight

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.DeterminantIntegerRows PaperP1.BidegreeOneFibreCount

theorem derivative_height (G : ℤ[X][X]) : height G.derivative ≤ degreeY G * height G := by
  apply PolynomialHeightArithmetic.bivariate_height_le
  intro i j
  have hc : G.derivative.coeff i = G.coeff (i + 1) * (((i + 1 : ℕ) : ℤ[X])) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Polynomial.coeff_derivative G i
  by_cases hi : i + 1 ≤ degreeY G
  · simp only [hc, Polynomial.coeff_mul_natCast, Int.natAbs_mul,
      Int.natAbs_natCast]
    exact (Nat.mul_le_mul_right _ (coefficient_natAbs_le_height G (i + 1) j)).trans (by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (height G) hi)
  · have hz : G.coeff (i + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
      change ¬i + 1 ≤ G.natDegree at hi
      omega)
    simp only [Polynomial.coeff_derivative, hz, zero_mul, Polynomial.coeff_zero,
      Int.natAbs_zero, Nat.zero_le]

theorem projective_evaluation_bound (G : ℤ[X][X]) (z : Point)
    (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (hx : ∀ c, |(z.1 c : ℝ)| ≤ L) (hy : ∀ c, |(z.2 c : ℝ)| ≤ Y) :
    |((MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) : ℤ) : ℝ)| ≤
        (degreeX G + 1) * (degreeY G + 1) * (height G : ℝ) * L ^ degreeX G * Y ^ degreeY G := by
  rw [← ProjectiveUnitCharts.integer_cast, ProjectiveUnitCharts.evaluation_sum]
  calc
    _ ≤ ∑ i : Exponent (degreeX G) (degreeY G),
        |((G.coeff i.2.val).coeff i.1.val : ℝ) * (z.1 0 : ℝ) ^ i.1.val *
          (z.1 1 : ℝ) ^ (degreeX G - i.1.val) * (z.2 0 : ℝ) ^ i.2.val *
          (z.2 1 : ℝ) ^ (degreeY G - i.2.val)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Exponent (degreeX G) (degreeY G), (height G : ℝ) * L ^ degreeX G * Y ^ degreeY G := by
      apply Finset.sum_le_sum
      intro i _
      have hc : |((G.coeff i.2.val).coeff i.1.val : ℝ)| ≤ (height G : ℝ) := by
        have hn := coefficient_natAbs_le_height G i.2.val i.1.val
        have hr : (((G.coeff i.2.val).coeff i.1.val).natAbs : ℝ) ≤ (height G : ℝ) := by exact_mod_cast hn
        simpa only [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] using hr
      simp only [abs_mul, abs_pow]
      calc
        _ ≤ (height G : ℝ) * L ^ i.1.val * L ^ (degreeX G - i.1.val) *
            Y ^ i.2.val * Y ^ (degreeY G - i.2.val) := by
          gcongr
          · exact hx 0
          · exact hx 1
          · exact hy 0
          · exact hy 1
        _ = _ := by
          have hi : i.1.val ≤ degreeX G := by have := i.1.isLt; omega
          have hj : i.2.val ≤ degreeY G := by have := i.2.isLt; omega
          calc
            _ = (height G : ℝ) * (L ^ i.1.val * L ^ (degreeX G - i.1.val)) *
                (Y ^ i.2.val * Y ^ (degreeY G - i.2.val)) := by ring
            _ = _ := by rw [← pow_add, ← pow_add, Nat.add_sub_of_le hi, Nat.add_sub_of_le hj]
    _ = _ := by simp [Exponent, mul_assoc]

theorem badInteger_bound (G : ℤ[X][X]) (hb : 0 < degreeY G) (z : Point)
    (L Y : ℝ) (hL : 1 ≤ L) (hY : 1 ≤ Y)
    (hx : ∀ c, |(z.1 c : ℝ)| ≤ L) (hy : ∀ c, |(z.2 c : ℝ)| ≤ Y) :
    |(SmoothResidueClasses.badInteger G z : ℝ)| ≤
      (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
        L ^ (degreeX G + 1) * Y ^ degreeY G := by
  have hd := projective_evaluation_bound G.derivative z L Y (by linarith) (by linarith) hx hy
  have hxdeg := BivariateCurveDegrees.degreeX_derivative_le G
  have hydeg : degreeY G.derivative + 1 ≤ degreeY G := by
    have hh := Polynomial.natDegree_derivative_le G
    change G.derivative.natDegree + 1 ≤ G.natDegree
    change 0 < G.natDegree at hb
    omega
  have hh := derivative_height G
  have hhR : (height G.derivative : ℝ) ≤ (degreeY G : ℝ) * height G := by exact_mod_cast hh
  have hxR : (degreeX G.derivative : ℝ) ≤ degreeX G := by exact_mod_cast hxdeg
  have hyR : (degreeY G.derivative : ℝ) ≤ degreeY G := by exact_mod_cast (Nat.le_of_succ_le hydeg)
  simp only [SmoothResidueClasses.badInteger, Int.cast_mul, abs_mul]
  calc
    _ ≤ L * Y * ((degreeX G.derivative + 1) * (degreeY G.derivative + 1) *
        (height G.derivative : ℝ) * L ^ degreeX G.derivative * Y ^ degreeY G.derivative) := by
      gcongr
      · exact hx 1
      · exact hy 1
    _ = (degreeX G.derivative + 1) * (degreeY G.derivative + 1) *
        (height G.derivative : ℝ) * L ^ (degreeX G.derivative + 1) * Y ^ (degreeY G.derivative + 1) := by
      rw [pow_succ, pow_succ]
      ring
    _ ≤ (degreeX G + 1) * (degreeY G + 1) * ((degreeY G : ℝ) * height G) *
        L ^ (degreeX G + 1) * Y ^ degreeY G := by
      gcongr
    _ = _ := by ring

theorem nonexceptional_bound (G : ℤ[X][X]) (hne : G ≠ 0) (hb : 0 < degreeY G)
    (z : Point) (hprim : (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hconstant : MvPolynomial.eval z.1 ((G.coeff 0).homogenize (degreeX G)) ≠ 0)
    (hleading : MvPolynomial.eval z.1 ((G.coeff (degreeY G)).homogenize (degreeX G)) ≠ 0)
    (L : ℝ) (hL : 1 ≤ L) (hx : ∀ c, |(z.1 c : ℝ)| ≤ L) :
    |(SmoothResidueClasses.badInteger G z : ℝ)| ≤
      (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) * L ^ (degreeX G + 1) *
        ((degreeX G + 1) * (height G : ℝ) * L ^ degreeX G) ^ degreeY G := by
  let Y : ℝ := (degreeX G + 1) * (height G : ℝ) * L ^ degreeX G
  have hheight : (1 : ℝ) ≤ height G := by
    exact_mod_cast GeometricBiformCoarseCount.height_pos G hne
  have hpow : (1 : ℝ) ≤ L ^ degreeX G := one_le_pow₀ hL
  have hY : 1 ≤ Y := by
    have ha : (1 : ℝ) ≤ degreeX G + 1 := by
      have hn : (0 : ℝ) ≤ degreeX G := Nat.cast_nonneg _
      linarith
    exact (by norm_num : (1 : ℝ) = 1 * 1 * 1).trans_le
      (mul_le_mul (mul_le_mul ha hheight (by norm_num) (by positivity)) hpow (by norm_num) (by positivity))
  exact badInteger_bound G hb z L Y hL hY hx
    (PrimitiveHomogeneousRootBound.fibre_height_bound G z.1 z.2 hprim hcurve hconstant hleading L
      (by linarith) hx)

end PaperP1.ProjectivePrimeHeight
