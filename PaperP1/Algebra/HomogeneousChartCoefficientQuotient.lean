module

public import PaperP1.Algebra.HomogeneousSplitRadicalChart
public import PaperP1.Algebra.QuadraticTowerQuotient
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # Specializing the homogenizing variable to one has exactly its stated kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousChartCoefficientQuotient

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalChart

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

theorem chart_surjective (F : Type*) [Field F] : Function.Surjective (chart F) := by
  apply Polynomial.map_surjective
  apply Polynomial.map_surjective
  intro a
  exact ⟨C a, by simp⟩

theorem chart_ker (F : Type*) [Field F] :
    RingHom.ker (chart F) = Ideal.span {(C (C (X : F[X])) : PolynomialRing F) - 1} := by
  simp only [chart, Polynomial.ker_mapRingHom, Polynomial.ker_evalRingHom,
    Ideal.map_span, Set.image_singleton, map_sub, map_one]

def coefficientQuotientEquiv (F : Type*) [Field F] :
    (PolynomialRing F) ⧸ Ideal.span {(C (C (X : F[X])) : PolynomialRing F) - 1} ≃+* F[X][X] :=
  (Ideal.quotEquivOfEq (chart_ker F).symm).trans
    ((chart F).quotientKerEquivOfSurjective (chart_surjective F))

theorem coefficientQuotientEquiv_mk (F : Type*) [Field F] (p : PolynomialRing F) :
    coefficientQuotientEquiv F (Ideal.Quotient.mk _ p) = chart F p := by
  rw [coefficientQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end PaperP1.HomogeneousChartCoefficientQuotient
