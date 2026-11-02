module

public import PaperP1.Arithmetic.CurveWordSeries
public import PaperP1.Algebra.CurveSeriesField
public import Mathlib.Tactic.Push

/-! # Functional squares force actual integer-offset matches on every regular fibre -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveSquareMatching

open Polynomial PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres PaperP1.CurveFibreRegularity
  PaperP1.CurveFormalBranch PaperP1.CurveFunctionField PaperP1.FormalWordPolynomials

local instance : CommRing ℤ[X][X] := inferInstance

theorem root_matches_offset {K : Type*} [Field K] [CharZero K] (C₀ : ℤ[X][X])
    [hC : Fact (Irreducible C₀)] (hy : 0 < degreeY C₀) (I J : Finset ℤ)
    (hsquare : IsSquare (specialize C₀ (wordOver ℤ I J))) (u : ℤ) (hu : u ∈ I)
    (hregular : u ∉ badOffsets C₀) (z : K) (hz : (fibre C₀ u).eval z = 0) :
    ∃ v ∈ J, z = -(v : K) := by
  by_contra hn
  push Not at hn
  obtain ⟨y, hconstant, hbranch⟩ := exists_branch C₀ hC.out hy u hregular z hz
  have hnot := CurveWordSeries.not_fraction_square_word I J u hu y z hconstant hn
  have hs := hsquare.map (CurveSeriesField.fieldMap C₀ hy u y hbranch)
  rw [CurveSeriesField.fieldMap_specialize] at hs
  exact hnot hs

end PaperP1.CurveSquareMatching
