module

public import PaperP1.Algebra.FirstChartCoordinateEquiv
public import PaperP1.Algebra.HomogeneousFirstChartTranslation

/-! # The exact linear-plus-quadratic equation at a smooth first-chart origin -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousQuadricFirstChart

open MvPolynomial Finset

variable {F : Type*} [Field F]

theorem decomposition (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2)
    (hroot : eval (Fin.cons 1 0) P = 0) :
    P = QuadricNormalHomogenization.polynomial
      ((finSuccEquiv F 3 P).coeff 1) ((finSuccEquiv F 3 P).coeff 0) := by
  have hdeg : (finSuccEquiv F 3 P).natDegree < 3 := by
    rw [natDegree_finSuccEquiv]
    exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree P 0).trans hP.totalDegree_le)
  have ht : (finSuccEquiv F 3 P).coeff 2 = 0 := by
    rw [HomogeneousLinearShear.top_coefficient P hP, hroot, map_zero]
  apply (finSuccEquiv F 3).injective
  simp only [QuadricNormalHomogenization.polynomial, map_add, map_mul,
    FirstChartCoordinateEquiv.finSucc_rename_succ, finSuccEquiv_X_zero]
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow' _ hdeg]
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one, ht, map_zero, zero_mul, add_zero]
  ring

theorem free_partial_rename (P : MvPolynomial (Fin 3) F) (i : Fin 3) :
    eval (Fin.cons 1 0) (pderiv i.succ (rename Fin.succ P)) =
      P.coeff (Finsupp.single i 1) := by
  rw [pderiv_rename (Fin.succ_injective 3) i P, eval_rename]
  change eval (0 : Fin 3 → F) (pderiv i P) = P.coeff (Finsupp.single i 1)
  rw [MvPolynomial.eval_zero]
  change (pderiv i P).coeff 0 = P.coeff (Finsupp.single i 1)
  simp only [coeff_pderiv, zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add,
    mul_one]

theorem origin_free_partial (L Q : MvPolynomial (Fin 3) F) (hQ : Q.IsHomogeneous 2)
    (i : Fin 3) :
    eval (Fin.cons 1 0) (pderiv i.succ (QuadricNormalHomogenization.polynomial L Q)) =
      L.coeff (Finsupp.single i 1) := by
  simp only [QuadricNormalHomogenization.polynomial, map_add, pderiv_mul,
    map_mul, free_partial_rename]
  have hz : pderiv i.succ (X (0 : Fin 4) : MvPolynomial (Fin 4) F) = 0 := by simp
  rw [hz, map_zero, zero_mul, zero_add, eval_X, Fin.cons_zero, one_mul]
  have hc : Q.coeff (Finsupp.single i 1) = 0 := hQ.coeff_eq_zero (by simp)
  rw [hc, zero_add]

theorem linear_part_nonzero (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2)
    (hroot : eval (Fin.cons 1 0) P = 0)
    (hgrad : ∃ i : Fin 3, eval (Fin.cons 1 0) (pderiv i.succ P) ≠ 0) :
    (finSuccEquiv F 3 P).coeff 1 ≠ 0 := by
  intro hz
  obtain ⟨i, hi⟩ := hgrad
  apply hi
  have hQ : ((finSuccEquiv F 3 P).coeff 0).IsHomogeneous 2 :=
    hP.finSuccEquiv_coeff_isHomogeneous 0 2 rfl
  conv_lhs => rw [decomposition P hP hroot]
  rw [origin_free_partial _ _ hQ i, hz]
  simp

end PaperP1.HomogeneousQuadricFirstChart
