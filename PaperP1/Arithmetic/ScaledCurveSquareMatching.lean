module

public import PaperP1.Arithmetic.CurveSquareMatching

/-! # Actual nonzero scalar coefficients preserve the regular-fibre square-matching obstruction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledCurveSquareMatching

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres PaperP1.CurveFibreRegularity
  PaperP1.CurveFormalBranch PaperP1.CurveFunctionField PaperP1.FormalWordPolynomials

def word (d : ℤ) (I J : Finset ℤ) : ℤ[X][X] := (d : ℤ[X][X]) * wordOver ℤ I J

theorem not_fraction_square_word {K : Type*} [Field K] [CharZero K]
    (d : ℤ) (hd : d ≠ 0) (I J : Finset ℤ) (u : ℤ) (hu : u ∈ I)
    (y : PowerSeries K) (z : K) (hz : PowerSeries.constantCoeff y = z)
    (hmismatch : ∀ j ∈ J, z ≠ -(j : K)) :
    ¬ IsSquare (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (evaluation u y (word d I J))) := by
  obtain ⟨v, hv, he⟩ := CurveWordSeries.exists_simple_factor I J u hu y z hz hmismatch
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  have hunit : IsUnit (d : PowerSeries K) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simpa only [map_intCast] using isUnit_iff_ne_zero.mpr hdK
  have hscaled : evaluation u y (word d I J) = PowerSeries.X * ((d : PowerSeries K) * v) := by
    rw [word, map_mul, map_intCast, he]
    ring
  rw [hscaled]
  exact PowerSeriesSquareGap.not_fraction_square _ (hunit.mul hv)

theorem root_matches_offset {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X])
    [hC : Fact (Irreducible C₀)] (hy : 0 < degreeY C₀) (d : ℤ) (hd : d ≠ 0) (I J : Finset ℤ)
    (hsquare : IsSquare (specialize C₀ (word d I J))) (u : ℤ) (hu : u ∈ I)
    (hregular : u ∉ badOffsets C₀) (z : K) (hz : (fibre C₀ u).eval z = 0) :
    ∃ v ∈ J, z = -(v : K) := by
  by_contra hn
  push Not at hn
  obtain ⟨y, hconstant, hbranch⟩ := exists_branch C₀ hC.out hy u hregular z hz
  have hnot := not_fraction_square_word d hd I J u hu y z hconstant hn
  have hs := hsquare.map (CurveSeriesField.fieldMap C₀ hy u y hbranch)
  rw [CurveSeriesField.fieldMap_specialize] at hs
  exact hnot hs

end PaperP1.ScaledCurveSquareMatching
