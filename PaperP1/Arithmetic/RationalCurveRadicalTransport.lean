module

public import PaperP1.Arithmetic.IntegerCurveFieldEquiv
public import PaperP1.Arithmetic.ScaledCurveEquationClasses
public import PaperP1.Algebra.FieldEquivScalarTransport
public import PaperP1.Algebra.ScaledSplitWordSquares

/-! # Literal rational plane-curve radical roots transport to the actual irreducible integer model -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalCurveRadicalTransport

open Polynomial PaperP1.FormalWordPolynomials

theorem rationalize_scaled_word (d : ℤ) (I J : Finset ℤ) :
    rationalize (ScaledCurveSquareMatching.word d I J) = ScaledSplitWordSquares.scaledPolynomial (d : ℚ) I J := by
  rw [ScaledCurveSquareMatching.word, map_mul, map_intCast, rationalize_word]
  rfl

def value {ι : Type*} (f : ℚ[X][X]) [Fact (Irreducible f)] (d : ι → ℤ) (I J : ι → Finset ℤ) (ν : ι) :
    AffineCurveFunctionField.FunctionField f :=
  AffineCurveFunctionField.specialize f (ScaledSplitWordSquares.scaledPolynomial (d ν : ℚ) (I ν) (J ν))

theorem equiv_value {ι : Type*} [Fintype ι] (P : ℤ[X][X]) [Fact (Irreducible P)]
    (f : ℚ[X][X]) [Fact (Irreducible f)] (hass : Associated (rationalize P) f)
    (d : ι → ℤ) (I J : ι → Finset ℤ) (ν : ι) :
    IntegerCurveFieldEquiv.equiv P f hass (ScaledCurveEquationClasses.value P d I J ν) = value f d I J ν := by
  change IntegerCurveFieldEquiv.equiv P f hass
    (CurveFunctionField.specialize P (ScaledCurveSquareMatching.word (d ν) (I ν) (J ν))) = _
  rw [IntegerCurveFieldEquiv.equiv_specialize, rationalize_scaled_word]
  rfl

theorem roots {ι L : Type*} [Fintype ι] (P : ℤ[X][X]) [Fact (Irreducible P)]
    (f : ℚ[X][X]) [Fact (Irreducible f)] (hass : Associated (rationalize P) f)
    [Field L] [Algebra (AffineCurveFunctionField.FunctionField f) L]
    (d : ι → ℤ) (I J : ι → Finset ℤ) (r : ι → L)
    (hr : ∀ ν, r ν ^ 2 = algebraMap (AffineCurveFunctionField.FunctionField f) L (value f d I J ν)) :
    letI := FieldEquivScalarTransport.algebra (L := L) (IntegerCurveFieldEquiv.equiv P f hass)
    ∀ ν, r ν ^ 2 = algebraMap (CurveFunctionField.FunctionField P) L (ScaledCurveEquationClasses.value P d I J ν) := by
  let := FieldEquivScalarTransport.algebra (L := L) (IntegerCurveFieldEquiv.equiv P f hass)
  intro ν
  rw [FieldEquivScalarTransport.algebraMap_eq, equiv_value]
  exact hr ν

end PaperP1.RationalCurveRadicalTransport
