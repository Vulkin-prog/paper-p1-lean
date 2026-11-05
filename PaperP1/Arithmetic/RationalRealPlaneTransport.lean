module

public import PaperP1.Arithmetic.IntegerCurveRationalization
public import PaperP1.Algebra.ScalarIrreducibilityReflection

/-! # Exact rational-to-real plane equations, degrees and integer populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalRealPlaneTransport

open Polynomial PolynomialScalarProjection

theorem complex_extension (Q : ℚ[X][X]) :
    (extend (extend Q : ℝ[X][X]) : ℂ[X][X]) = (extend Q : ℂ[X][X]) := by
  ext i j
  rw [extend_coefficient, extend_coefficient, extend_coefficient]
  exact (IsScalarTower.algebraMap_apply ℚ ℝ ℂ _).symm

theorem real_irreducible (Q : ℚ[X][X]) (hgeo : Irreducible (extend Q : ℂ[X][X])) :
    Irreducible (extend Q : ℝ[X][X]) := by
  apply ScalarIrreducibilityReflection.irreducible_of_extension (L := ℂ)
  rw [complex_extension]
  exact hgeo

theorem real_degree (Q : ℚ[X][X]) :
    PlaneCurvePointCount.degree (extend Q : ℝ[X][X]) = PlaneCurvePointCount.degree Q :=
  IntegerCurveRationalization.degree_coefficientMap (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective Q

theorem real_grid (Q : ℚ[X][X]) (N : ℕ) :
    PlaneCurvePointCount.grid (extend Q : ℝ[X][X]) N = PlaneCurvePointCount.grid Q N :=
  IntegerCurveRationalization.grid_coefficientMap (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective Q N

end PaperP1.RationalRealPlaneTransport
