module

public import PaperP1.Algebra.BivariateResultantDegree
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Tactic.FinCases

/-! # Exact total degree in a nested-polynomial coordinate chart

Coordinate zero is the outer variable and coordinate one is the inner variable.
Both the coefficient formula and the actual finite-support total degree agree.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateTotalDegreeChart

open Polynomial

variable (R : Type*) [CommRing R]

def chart : MvPolynomial (Fin 2) R ≃ₐ[R] R[X][X] :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

variable {R}

theorem chart_coefficient (f : MvPolynomial (Fin 2) R) (y x : ℕ) :
    (((chart R f).coeff y).coeff x) =
      f.coeff ((Finsupp.single (0 : Fin 1) x).cons y) := by
  change (((Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 f)).coeff y).coeff x) = _
  rw [Polynomial.coeff_map]
  change ((MvPolynomial.uniqueAlgEquiv R (Fin 1)
    ((MvPolynomial.finSuccEquiv R 1 f).coeff y)).coeff x) = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, MvPolynomial.finSuccEquiv_coeff_coeff]
  rfl

theorem chart_X_zero : chart R (MvPolynomial.X 0) = (Polynomial.X : R[X][X]) := by
  simp [chart, MvPolynomial.finSuccEquiv_X_zero]

theorem chart_X_one : chart R (MvPolynomial.X 1) = Polynomial.C (Polynomial.X : R[X]) := by
  change (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp

theorem chart_degree (f : MvPolynomial (Fin 2) R) :
    PlaneCurvePointCount.degree (chart R f) = f.totalDegree := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    have hrow : (chart R f).coeff y ≠ 0 := Polynomial.mem_support_iff.mp hy
    have hc : (((chart R f).coeff y).coeff ((chart R f).coeff y).natDegree) ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hrow
    rw [chart_coefficient] at hc
    have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
    simpa [Finsupp.sum_cons, add_comm] using hd
  · apply Finset.sup_le
    intro m hm
    have hmrepr : m = (Finsupp.single (0 : Fin 1) (m 1)).cons (m 0) := by
      ext i
      fin_cases i
      · simp
      · change m 1 = (Finsupp.single (0 : Fin 1) (m 1)).cons (m 0) (Fin.succ 0)
        rw [Finsupp.cons_succ, Finsupp.single_eq_same]
    have hc : (((chart R f).coeff (m 0)).coeff (m 1)) ≠ 0 := by
      rw [chart_coefficient, ← hmrepr]
      exact MvPolynomial.mem_support_iff.mp hm
    have hrow : (chart R f).coeff (m 0) ≠ 0 := fun hz ↦ hc (by rw [hz, coeff_zero])
    have hx := Polynomial.le_natDegree_of_ne_zero hc
    have hd := BivariateResultantDegree.coefficient_row_degree (chart R f) (m 0) hrow
    have hs : m.sum (fun _ e ↦ e) = m 0 + m 1 := by
      conv_lhs => rw [hmrepr]
      simp [Finsupp.sum_cons]
    rw [hs]
    omega

theorem chart_evaluation (f : MvPolynomial (Fin 2) R) (x y : R) :
    (chart R f).evalEval x y = MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 ↦ x)) f := by
  have he : (Polynomial.evalEvalRingHom x y).comp (chart R).toRingHom =
      MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 ↦ x)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hc : chart R (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) :=
        (chart R).commutes a
      change (chart R (MvPolynomial.C a)).evalEval x y =
        MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 ↦ x)) (MvPolynomial.C a)
      rw [hc, Polynomial.evalEval_CC, MvPolynomial.eval_C]
    · intro i
      fin_cases i <;> simp [RingHom.comp_apply, chart_X_zero, chart_X_one]
  exact RingHom.congr_fun he f

end PaperP1.BivariateTotalDegreeChart
