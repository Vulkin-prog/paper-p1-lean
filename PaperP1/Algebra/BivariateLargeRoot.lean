module

public import PaperP1.Algebra.PolynomialHeightArithmetic

/-! # A polynomial through a sufficiently large integer point uses both variables -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateLargeRoot

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.PolynomialHeightArithmetic

theorem height_swap_le (P : ℤ[X][X]) : height (Bivariate.swap P) ≤ height P := by
  apply bivariate_height_le
  intro i j
  rw [coeff_swap]
  exact coefficient_natAbs_le_height P j i

theorem height_swap (P : ℤ[X][X]) : height (Bivariate.swap P) = height P := by
  apply le_antisymm (height_swap_le P)
  simpa only [Bivariate.swap_swap_apply] using height_swap_le (Bivariate.swap P)

theorem eval_swap (P : ℤ[X][X]) (x y : ℤ) :
    (Bivariate.swap P).evalEval x y = P.evalEval y x := by
  simpa only [coe_aevalAeval_eq_evalEval] using Bivariate.aevalAeval_swap x y P

theorem degreeY_pos (P : ℤ[X][X]) (hP : P ≠ 0) (x y : ℤ) (hz : P.evalEval x y = 0)
    (hx : height P < x.natAbs) : 0 < degreeY P := by
  by_contra hn
  have hd : P.natDegree = 0 := by change ¬ 0 < P.natDegree at hn; omega
  have hC := eq_C_of_natDegree_eq_zero hd
  have hp : P.coeff 0 ≠ 0 := by
    intro h
    apply hP
    rw [hC, h, C_0]
  have he : (P.coeff 0).IsRoot x := by
    change (P.coeff 0).eval x = 0
    rwa [hC, evalEval_C] at hz
  have hroot := PaperP1.integerRoot_natAbs_le_height hp he
  have hheight := row_height_le P 0
  omega

theorem degreeX_pos (P : ℤ[X][X]) (hP : P ≠ 0) (x y : ℤ) (hz : P.evalEval x y = 0)
    (hy : height P < y.natAbs) : 0 < degreeX P := by
  have hs : Bivariate.swap P ≠ 0 := by
    intro h
    exact hP ((Bivariate.swap (R := ℤ)).injective (h.trans (map_zero _).symm))
  have he : (Bivariate.swap P).evalEval y x = 0 := by rw [eval_swap, hz]
  have hh : height (Bivariate.swap P) < y.natAbs := by rwa [height_swap]
  exact degreeY_pos (Bivariate.swap P) hs y x he hh

theorem both_degrees_pos (P : ℤ[X][X]) (hP : P ≠ 0) (x y : ℤ) (hz : P.evalEval x y = 0)
    (hx : height P < x.natAbs) (hy : height P < y.natAbs) :
    0 < degreeX P ∧ 0 < degreeY P := ⟨degreeX_pos P hP x y hz hy, degreeY_pos P hP x y hz hx⟩

end PaperP1.BivariateLargeRoot
