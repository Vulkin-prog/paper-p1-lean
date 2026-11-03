module

public import PaperP1.Algebra.BivariateDegrees
public import PaperP1.Algebra.ReducedQuotientGraph
public import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Actual reduced rational numerator and denominator of an irreducible integer curve linear in Y -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerGraphEquation

open Polynomial PaperP1.BivariateDegrees

def numerator (C₀ : ℤ[X][X]) : ℚ[X] := -(C₀.coeff 0).map (Int.castRingHom ℚ)

def denominator (C₀ : ℤ[X][X]) : ℚ[X] := (C₀.coeff 1).map (Int.castRingHom ℚ)

def function (C₀ : ℤ[X][X]) : RatFunc ℚ := RationalMapFieldDegree.quotient (numerator C₀) (denominator C₀)

theorem eval_formula (C₀ : ℤ[X][X]) (hY : degreeY C₀ = 1) (x y : ℤ) :
    C₀.evalEval x y = (C₀.coeff 1).eval x * y + (C₀.coeff 0).eval x := by
  have hform := Polynomial.eq_X_add_C_of_natDegree_le_one (p := C₀) hY.le
  exact (congrArg (fun P : ℤ[X][X] ↦ P.evalEval x y) hform).trans
    (by simp only [evalEval_add, evalEval_mul, evalEval_C, evalEval_X])

theorem denominator_ne_zero (C₀ : ℤ[X][X]) (hY : degreeY C₀ = 1) : denominator C₀ ≠ 0 := by
  apply (Polynomial.map_ne_zero_iff Int.cast_injective).mpr
  have hC : C₀ ≠ 0 := by
    intro hz
    change C₀.natDegree = 1 at hY
    rw [hz, natDegree_zero] at hY
    omega
  have hc : C₀.coeff C₀.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hC
  change C₀.natDegree = 1 at hY
  simpa only [hY] using hc

theorem coefficient_ne_zero_at_point (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hY : degreeY C₀ = 1)
    (x y : ℤ) (hpoint : C₀.evalEval x y = 0) : (C₀.coeff 1).eval x ≠ 0 := by
  intro hzero
  have hz0 : (C₀.coeff 0).eval x = 0 := by
    rw [eval_formula C₀ hY x y, hzero, zero_mul, zero_add] at hpoint
    exact hpoint
  have hdiv0 : X - C x ∣ C₀.coeff 0 := Polynomial.dvd_iff_isRoot.mpr hz0
  have hdiv1 : X - C x ∣ C₀.coeff 1 := Polynomial.dvd_iff_isRoot.mpr hzero
  have hdiv : C (X - C x) ∣ C₀ := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one (p := C₀) hY.le]
    exact dvd_add (dvd_mul_of_dvd_left (_root_.map_dvd C hdiv1) X) (_root_.map_dvd C hdiv0)
  have hnonunit : ¬ IsUnit (C (X - C x) : ℤ[X][X]) := by
    intro hu
    exact not_isUnit_of_natDegree_pos (X - C x : ℤ[X]) (by rw [natDegree_X_sub_C]; decide) (isUnit_C.mp hu)
  have hass := ((Fact.out : Irreducible C₀).dvd_iff.mp hdiv).resolve_left hnonunit
  have hdegree := natDegree_le_of_dvd hass.dvd (C_ne_zero.mpr (X_sub_C_ne_zero x))
  rw [natDegree_C] at hdegree
  change C₀.natDegree = 1 at hY
  omega

theorem original_point (C₀ : ℤ[X][X]) (hY : degreeY C₀ = 1) (x y : ℤ)
    (hpoint : C₀.evalEval x y = 0) : (numerator C₀).eval (x : ℚ) = (y : ℚ) * (denominator C₀).eval (x : ℚ) := by
  have hp : (C₀.coeff 1).eval x * y + (C₀.coeff 0).eval x = 0 := (eval_formula C₀ hY x y).symm.trans hpoint
  have hpQ : (((C₀.coeff 1).eval x : ℤ) : ℚ) * (y : ℚ) + (((C₀.coeff 0).eval x : ℤ) : ℚ) = 0 := by
    exact_mod_cast hp
  simp only [numerator, denominator, eval_neg, eval_intCast_map]
  linear_combination -hpQ

theorem denominator_nonvanishing (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hY : degreeY C₀ = 1)
    (x y : ℤ) (hpoint : C₀.evalEval x y = 0) : (denominator C₀).eval (x : ℚ) ≠ 0 := by
  change ((C₀.coeff 1).map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) x) ≠ 0
  rw [Polynomial.eval_map_apply]
  exact (Int.cast_ne_zero).mpr (coefficient_ne_zero_at_point C₀ hY x y hpoint)

theorem reduced_point (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (hY : degreeY C₀ = 1)
    (x y : ℤ) (hpoint : C₀.evalEval x y = 0) :
    (function C₀).num.eval (x : ℚ) = (y : ℚ) * (function C₀).denom.eval (x : ℚ) :=
  ReducedQuotientGraph.point_equation (numerator C₀) (denominator C₀) (denominator_ne_zero C₀ hY) _ _
    (denominator_nonvanishing C₀ hY x y hpoint) (original_point C₀ hY x y hpoint)

theorem reduced_degree_le (C₀ : ℤ[X][X]) (hY : degreeY C₀ = 1) :
    max (function C₀).num.natDegree (function C₀).denom.natDegree ≤ degreeX C₀ := by
  apply (ReducedQuotientGraph.degree_le (numerator C₀) (denominator C₀) (denominator_ne_zero C₀ hY)).trans
  apply max_le
  · have hp : (numerator C₀).natDegree ≤ (C₀.coeff 0).natDegree := by
      simpa only [numerator, natDegree_neg] using
        (natDegree_map_le (p := C₀.coeff 0) (f := Int.castRingHom ℚ))
    exact hp.trans (natDegree_coeff_le_degreeX C₀ 0)
  · have hqdeg : (denominator C₀).natDegree ≤ (C₀.coeff 1).natDegree := natDegree_map_le
    exact hqdeg.trans (natDegree_coeff_le_degreeX C₀ 1)

end PaperP1.IntegerGraphEquation
