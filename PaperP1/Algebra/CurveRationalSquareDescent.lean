module

public import PaperP1.Algebra.AffineCurveFractionParametrization
public import PaperP1.Algebra.OddDegreeFieldSquares

/-! # Actual radical roots over an odd-degree curve cover give literal rational-graph squares -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveRationalSquareDescent

open Polynomial PaperP1.AffineCurveFunctionField

variable {F K : Type*} [Field F] [Field K]

theorem value_isSquare (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree)
    (p q : F[X]) (hq : q ≠ 0)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q)
    [Algebra (FunctionField C₀) K] (hodd : Odd (Module.finrank (FunctionField C₀) K))
    (c : F) (I : Finset ℤ) (j : ℤ) (r : K)
    (hr : r ^ 2 = algebraMap (FunctionField C₀) K
      (specialize C₀ (ScaledSplitWordSquares.scaledPolynomial c I {j}))) :
    IsSquare (RationalGraphSquareRoots.value c (j : F) (FormalWordPolynomials.linearOver F I) p q) := by
  apply (AffineCurveFractionParametrization.value_isSquare_iff C₀ hdegree p q hq hgraph c I j).mpr
  exact (OddDegreeFieldSquares.isSquare_iff hodd _).mp ⟨r, by simpa only [pow_two] using hr.symm⟩

end PaperP1.CurveRationalSquareDescent
