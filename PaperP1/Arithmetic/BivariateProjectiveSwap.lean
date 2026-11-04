module

public import PaperP1.Arithmetic.IntegerPairFactorCharts
public import PaperP1.Algebra.BivariateLargeRoot

/-! # Literal projective evaluation commutes with exchange of the two pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateProjectiveSwap

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.IntegerFactorProjectiveCurve
open PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform

theorem degreeX_swap (G : ℤ[X][X]) : degreeX (Bivariate.swap G) = degreeY G := by
  simp only [degreeX, degreeY, Bivariate.swap_swap_apply]

theorem degreeY_swap (G : ℤ[X][X]) : degreeY (Bivariate.swap G) = degreeX G := rfl

theorem biform_evaluation_swap (a b : ℕ) (w : Exponent a b → ℤ) (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) y (biform b a (fun i ↦ w (i.2, i.1))) =
      MvPolynomial.eval₂ (MvPolynomial.eval y) x (biform a b w) := by
  rw [IntegerPairFactorCharts.evaluation_sum, IntegerPairFactorCharts.evaluation_sum]
  simp only [Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem evaluation_swap (G : ℤ[X][X]) (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) y (projective (Bivariate.swap G)) =
      MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) := by
  unfold IntegerFactorProjectiveCurve.projective
  unfold IntegerFactorProjectiveCurve.coefficients
  unfold degreeX degreeY
  rw [Bivariate.swap_swap_apply]
  have hs := biform_evaluation_swap _ _ (coefficients G) x y
  unfold IntegerFactorProjectiveCurve.coefficients degreeX degreeY at hs
  simpa only [coeff_swap] using hs

end PaperP1.BivariateProjectiveSwap
