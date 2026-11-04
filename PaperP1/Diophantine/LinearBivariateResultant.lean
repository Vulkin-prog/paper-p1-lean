module

public import PaperP1.Algebra.LinearBivariateCoefficients
public import PaperP1.Diophantine.ResultantDivisibility
public import PaperP1.Diophantine.ReflectedResultants

/-! # Both resultant certificates are nonzero for the actual first-degree-one factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearBivariateResultant

open Polynomial PaperP1.BivariateDegrees PaperP1.LinearBivariateCoefficients

theorem actual_resultant_ne_zero (G : ℤ[X][X]) (hG : Irreducible G)
    (hfirst : degreeX G = 1) (hsecond : 0 < degreeY G) :
    (firstCoefficient G).resultant (secondCoefficient G) (degreeY G) (degreeY G) ≠ 0 := by
  have hb := coefficient_degree_bounds G
  exact ResultantDivisibility.integer_padded_resultant_ne_zero (firstCoefficient G) (secondCoefficient G)
    (degreeY G) hsecond hb.1 hb.2 (coefficient_full_degree G hfirst) (coefficients_coprime G hG hfirst)

theorem reflected_actual_resultant_ne_zero (G : ℤ[X][X]) (hG : Irreducible G)
    (hfirst : degreeX G = 1) (hsecond : 0 < degreeY G) :
    ((firstCoefficient G).reflect (degreeY G)).resultant ((secondCoefficient G).reflect (degreeY G))
      (degreeY G) (degreeY G) ≠ 0 :=
  ReflectedResultants.reflected_resultant_ne_zero _ _ _ (actual_resultant_ne_zero G hG hfirst hsecond)

end PaperP1.LinearBivariateResultant
