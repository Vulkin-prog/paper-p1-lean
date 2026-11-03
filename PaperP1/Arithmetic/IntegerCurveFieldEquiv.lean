module

public import PaperP1.Arithmetic.IntegerCurveLift
public import PaperP1.Algebra.LocalizedQuotientFractionEquiv
public import PaperP1.Algebra.AffineCurveFunctionField
public import PaperP1.Algebra.CurveFunctionField

/-! # Actual integer and rational plane-equation quotient fraction fields agree, including literal polynomial values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCurveFieldEquiv

open Polynomial PaperP1.FormalWordPolynomials

attribute [local instance] Polynomial.algebra

def innerDenominators : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map Polynomial.C

def denominators : Submonoid ℤ[X][X] := innerDenominators.map Polynomial.C

local instance innerLocalization : IsLocalization innerDenominators ℚ[X] :=
  Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ

local instance outerLocalization : IsLocalization denominators ℚ[X][X] :=
  Polynomial.isLocalization innerDenominators ℚ[X]

local instance integerCoordinateRing (P : ℤ[X][X]) : CommRing (CurveFunctionField.CoordinateRing P) := inferInstance
local instance rationalCoordinateRing (f : ℚ[X][X]) : CommRing (AffineCurveFunctionField.CoordinateRing f) := inferInstance
local instance mappedCoordinateRing (P : ℤ[X][X]) :
    CommRing (ℚ[X][X] ⧸ (CurveFunctionField.curveIdeal P).map (algebraMap ℤ[X][X] ℚ[X][X])) := inferInstance

theorem mappedIdeal_eq (P : ℤ[X][X]) (f : ℚ[X][X]) (hass : Associated (rationalize P) f) :
    (CurveFunctionField.curveIdeal P).map (algebraMap ℤ[X][X] ℚ[X][X]) = AffineCurveFunctionField.ideal f := by
  rw [CurveFunctionField.curveIdeal, Ideal.map_span, Set.image_singleton, AffineCurveFunctionField.ideal]
  exact Ideal.span_singleton_eq_span_singleton.mpr hass

theorem denominators_disjoint (P : ℤ[X][X]) (f : ℚ[X][X]) [Fact (Irreducible f)]
    (hass : Associated (rationalize P) f) :
    Disjoint (denominators : Set ℤ[X][X]) (CurveFunctionField.curveIdeal P : Set ℤ[X][X]) := by
  apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint denominators ℚ[X][X] (CurveFunctionField.curveIdeal P)).mp
  rw [mappedIdeal_eq P f hass]
  exact (AffineCurveFunctionField.ideal_isPrime f).ne_top

def coordinateEquiv (P : ℤ[X][X]) (f : ℚ[X][X]) (hass : Associated (rationalize P) f) :
    (ℚ[X][X] ⧸ (CurveFunctionField.curveIdeal P).map (algebraMap ℤ[X][X] ℚ[X][X])) ≃+*
      AffineCurveFunctionField.CoordinateRing f := Ideal.quotEquivOfEq (mappedIdeal_eq P f hass)

def equiv (P : ℤ[X][X]) [Fact (Irreducible P)] (f : ℚ[X][X]) [Fact (Irreducible f)]
    (hass : Associated (rationalize P) f) :
    CurveFunctionField.FunctionField P ≃+* AffineCurveFunctionField.FunctionField f :=
  (LocalizedQuotientFractionEquiv.equiv (S := ℚ[X][X]) denominators (CurveFunctionField.curveIdeal P)
    (denominators_disjoint P f hass)).trans
      (IsFractionRing.ringEquivOfRingEquiv
        (A := ℚ[X][X] ⧸ (CurveFunctionField.curveIdeal P).map (algebraMap ℤ[X][X] ℚ[X][X]))
        (B := AffineCurveFunctionField.CoordinateRing f)
        (K := FractionRing (ℚ[X][X] ⧸ (CurveFunctionField.curveIdeal P).map (algebraMap ℤ[X][X] ℚ[X][X])))
        (L := AffineCurveFunctionField.FunctionField f) (coordinateEquiv P f hass))

theorem equiv_specialize (P : ℤ[X][X]) [Fact (Irreducible P)] (f : ℚ[X][X]) [Fact (Irreducible f)]
    (hass : Associated (rationalize P) f) (q : ℤ[X][X]) :
    equiv P f hass (CurveFunctionField.specialize P q) = AffineCurveFunctionField.specialize f (rationalize q) := by
  change equiv P f hass (algebraMap (CurveFunctionField.CoordinateRing P) (CurveFunctionField.FunctionField P)
    (Ideal.Quotient.mk _ q)) = _
  rw [equiv, RingEquiv.trans_apply, LocalizedQuotientFractionEquiv.equiv_mk,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rw [coordinateEquiv, Ideal.quotEquivOfEq_mk]
  rfl

theorem isSquare_iff (P : ℤ[X][X]) [Fact (Irreducible P)] (f : ℚ[X][X]) [Fact (Irreducible f)]
    (hass : Associated (rationalize P) f) (q : ℤ[X][X]) :
    IsSquare (CurveFunctionField.specialize P q) ↔ IsSquare (AffineCurveFunctionField.specialize f (rationalize q)) := by
  rw [← equiv_specialize P f hass q]
  constructor
  · intro hs
    exact hs.map (equiv P f hass)
  · intro hs
    simpa only [RingEquiv.symm_apply_apply] using hs.map (equiv P f hass).symm

end PaperP1.IntegerCurveFieldEquiv
