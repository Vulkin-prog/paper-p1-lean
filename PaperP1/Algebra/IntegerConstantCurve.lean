module

public import PaperP1.Algebra.CurveFunctionField
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Actual coordinate and function fields of constant-coordinate integer curves with an integer point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerConstantCurve

open Polynomial PaperP1.BivariateDegrees PaperP1.CurveFunctionField

local instance coordinateRing (C₀ : ℤ[X][X]) : CommRing (CoordinateRing C₀) := inferInstance

def verticalMap (x : ℤ) : ℤ[X][X] →+* ℤ[X] := mapRingHom (evalRingHom x)

def horizontalMap (y : ℤ) : ℤ[X][X] →+* ℤ[X] := evalRingHom (C y)

theorem verticalMap_kernel (x : ℤ) : RingHom.ker (verticalMap x) = Ideal.span {C (X - C x)} := by
  simp only [verticalMap, ker_mapRingHom, ker_evalRingHom, Ideal.map_span, Set.image_singleton]

theorem horizontalMap_kernel (y : ℤ) : RingHom.ker (horizontalMap y) = Ideal.span {X - C (C y)} :=
  ker_evalRingHom _

theorem verticalMap_surjective (x : ℤ) : Function.Surjective (verticalMap x) := by
  apply Polynomial.map_surjective
  intro a
  exact ⟨C a, by simp⟩

theorem horizontalMap_surjective (y : ℤ) : Function.Surjective (horizontalMap y) := by
  intro P
  exact ⟨C P, eval_C⟩

theorem ideal_vertical (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (x y : ℤ)
    (hY : degreeY C₀ = 0) (hpoint : C₀.evalEval x y = 0) :
    curveIdeal C₀ = RingHom.ker (verticalMap x) := by
  have hform : C₀ = C (C₀.coeff 0) := eq_C_of_natDegree_eq_zero hY
  have hz : (C₀.coeff 0).eval x = 0 := by
    rw [hform, evalEval_C] at hpoint
    exact hpoint
  have hdvd : C (X - C x) ∣ C₀ := hform ▸ _root_.map_dvd C (dvd_iff_isRoot.mpr hz)
  have hnu : ¬ IsUnit (C (X - C x) : ℤ[X][X]) := by
    intro hu
    exact not_isUnit_of_natDegree_pos (X - C x : ℤ[X])
      (by rw [natDegree_X_sub_C]; decide) (isUnit_C.mp hu)
  have hass := ((Fact.out : Irreducible C₀).dvd_iff.mp hdvd).resolve_left hnu
  rw [verticalMap_kernel]
  exact Ideal.span_singleton_eq_span_singleton.mpr hass

theorem ideal_horizontal (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (x y : ℤ)
    (hX : degreeX C₀ = 0) (hpoint : C₀.evalEval x y = 0) :
    curveIdeal C₀ = RingHom.ker (horizontalMap y) := by
  let p := (Bivariate.swap C₀).coeff 0
  have hform : C₀ = p.map C := by
    have h := congrArg (Bivariate.swap (R := ℤ)) (eq_C_of_natDegree_eq_zero hX)
    simpa only [Bivariate.swap_swap_apply, Bivariate.swap_C] using h
  have hz : p.eval y = 0 := by
    rw [hform, evalEval_map_C] at hpoint
    exact hpoint
  have hdvd : X - C (C y) ∣ C₀ := by
    rw [hform]
    simpa only [coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using
      _root_.map_dvd (Polynomial.mapRingHom C) (dvd_iff_isRoot.mpr hz)
  have hnu : ¬ IsUnit (X - C (C y) : ℤ[X][X]) :=
    not_isUnit_of_natDegree_pos _ (by rw [natDegree_X_sub_C]; decide)
  have hass := ((Fact.out : Irreducible C₀).dvd_iff.mp hdvd).resolve_left hnu
  rw [horizontalMap_kernel]
  exact Ideal.span_singleton_eq_span_singleton.mpr hass

def coordinateEquiv (C₀ : ℤ[X][X]) (φ : ℤ[X][X] →+* ℤ[X])
    (hker : curveIdeal C₀ = RingHom.ker φ) (hsurj : Function.Surjective φ) :
    CoordinateRing C₀ ≃+* ℤ[X] :=
  (Ideal.quotEquivOfEq hker).trans (φ.quotientKerEquivOfSurjective hsurj)

theorem coordinateEquiv_mk (C₀ : ℤ[X][X]) (φ : ℤ[X][X] →+* ℤ[X])
    (hker : curveIdeal C₀ = RingHom.ker φ) (hsurj : Function.Surjective φ) (P : ℤ[X][X]) :
    coordinateEquiv C₀ φ hker hsurj (Ideal.Quotient.mk _ P) = φ P := by
  rw [coordinateEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

def functionEquiv (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (φ : ℤ[X][X] →+* ℤ[X])
    (hker : curveIdeal C₀ = RingHom.ker φ) (hsurj : Function.Surjective φ) :
    FunctionField C₀ ≃+* FractionRing ℤ[X] :=
  IsFractionRing.ringEquivOfRingEquiv (K := FunctionField C₀) (L := FractionRing ℤ[X])
    (coordinateEquiv C₀ φ hker hsurj)

theorem functionEquiv_specialize (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)] (φ : ℤ[X][X] →+* ℤ[X])
    (hker : curveIdeal C₀ = RingHom.ker φ) (hsurj : Function.Surjective φ) (P : ℤ[X][X]) :
    functionEquiv C₀ φ hker hsurj (specialize C₀ P) = algebraMap ℤ[X] (FractionRing ℤ[X]) (φ P) := by
  change IsFractionRing.ringEquivOfRingEquiv (K := FunctionField C₀) (L := FractionRing ℤ[X])
    (coordinateEquiv C₀ φ hker hsurj)
    (algebraMap (CoordinateRing C₀) (FunctionField C₀) (Ideal.Quotient.mk _ P)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, coordinateEquiv_mk]

end PaperP1.IntegerConstantCurve
