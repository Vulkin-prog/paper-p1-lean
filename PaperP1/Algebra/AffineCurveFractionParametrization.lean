module

public import PaperP1.Algebra.AffineCurveFieldGeneration
public import PaperP1.Algebra.RationalGraphSquareRoots
public import PaperP1.Algebra.ScaledSplitWordSquares

/-! # Literal split radical polynomials on an actual curve become the actual rational-graph functions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineCurveFractionParametrization

open Polynomial PaperP1.AffineCurveFunctionField

variable {F : Type*} [Field F] (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree)
    (p q : F[X]) (hq : q ≠ 0)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q)

def equiv : FractionRing F[X] ≃ₐ[F] FunctionField C₀ :=
  (IsFractionRing.algEquivOfAlgEquiv (K := FractionRing F[X]) (L := RatFunc F)
    (AlgEquiv.refl : F[X] ≃ₐ[F] F[X])).trans
    (AffineCurveFieldGeneration.rationalEquiv C₀ hdegree p q hq hgraph)

theorem equiv_polynomial (P : F[X]) :
    equiv C₀ hdegree p q hq hgraph (algebraMap F[X] (FractionRing F[X]) P) = aeval (firstCoordinate C₀) P := by
  rw [equiv, AlgEquiv.trans_apply, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change RationalGraphFieldTower.evaluation (firstCoordinate C₀) (first_transcendental C₀ hdegree)
    (algebraMap F[X] (RatFunc F) P) = _
  exact RationalGraphFieldTower.evaluation_polynomial _ _ P

include hdegree hq hgraph in
theorem quotient_eq_coordinate :
    aeval (firstCoordinate C₀) p / aeval (firstCoordinate C₀) q = secondCoordinate C₀ := by
  have hn : aeval (firstCoordinate C₀) q ≠ 0 := by
    intro hz
    apply hq
    apply transcendental_iff_injective.mp (first_transcendental C₀ hdegree)
    simpa only [map_zero] using hz
  exact (div_eq_iff hn).mpr hgraph

theorem equiv_value (c : F) (I : Finset ℤ) (j : ℤ) :
    equiv C₀ hdegree p q hq hgraph
      (RationalGraphSquareRoots.value c (j : F) (FormalWordPolynomials.linearOver F I) p q) =
      specialize C₀ (ScaledSplitWordSquares.scaledPolynomial c I {j}) := by
  simp only [RationalGraphSquareRoots.value, map_mul, map_add, map_div₀, equiv_polynomial]
  rw [quotient_eq_coordinate C₀ hdegree p q hq hgraph]
  rw [← coordinates_evaluation]
  simp only [ScaledSplitWordSquares.scaledPolynomial, FormalWordPolynomials.wordOver,
    FormalWordPolynomials.linearOver, Finset.prod_singleton, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, map_mul, map_add, Polynomial.aevalAeval_C,
    Polynomial.aevalAeval_Y, aeval_C]
  ring

include hdegree hq hgraph in
theorem value_isSquare_iff (c : F) (I : Finset ℤ) (j : ℤ) :
    IsSquare (RationalGraphSquareRoots.value c (j : F) (FormalWordPolynomials.linearOver F I) p q) ↔
      IsSquare (specialize C₀ (ScaledSplitWordSquares.scaledPolynomial c I {j})) := by
  constructor
  · intro hs
    exact equiv_value C₀ hdegree p q hq hgraph c I j ▸ hs.map (equiv C₀ hdegree p q hq hgraph).toRingHom
  · intro hs
    rw [← equiv_value C₀ hdegree p q hq hgraph c I j] at hs
    simpa only [AlgEquiv.symm_apply_apply] using hs.map (equiv C₀ hdegree p q hq hgraph).symm

end PaperP1.AffineCurveFractionParametrization
