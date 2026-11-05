module

public import PaperP1.Algebra.FiniteBivariateScalarDecomposition
public import PaperP1.Algebra.BivariateResultantDegree
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Scalar components retain every base-field zero and never increase total degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarComponentPoints

open Polynomial Finset Module PaperP1.PolynomialScalarProjection

theorem project_monomial {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Module R A] [Module R B] (ell : A →ₗ[R] B) (n : ℕ) (c : A) :
    project ell (Polynomial.monomial n c) = Polynomial.monomial n (ell c) := by
  ext i
  simp only [project_coefficient, Polynomial.coeff_monomial]
  by_cases h : n = i <;> simp only [h, ite_true, ite_false, map_zero]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem project_evaluation (ell : L →ₗ[K] K) (P : L[X]) (x : K) :
    (project ell P).eval x = ell (P.eval (algebraMap K L x)) := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [project_add, Polynomial.eval_add, Polynomial.eval_add, map_add, hP, hQ]
  | monomial n c =>
    rw [project_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
    have he := ell.map_smul (x ^ n) c
    simpa [Algebra.smul_def, mul_comm] using he.symm

theorem component_monomial (ell : L →ₗ[K] K) (n : ℕ) (Q : L[X]) :
    component ell (Polynomial.monomial n Q) = Polynomial.monomial n (project ell Q) :=
  project_monomial (linearMap ell) n Q

theorem component_evaluation (ell : L →ₗ[K] K) (P : L[X][X]) (x y : K) :
    (component ell P).evalEval x y = ell (P.evalEval (algebraMap K L x) (algebraMap K L y)) := by
  classical
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, Polynomial.evalEval_add, Polynomial.evalEval_add, map_add, hP, hQ]
  | monomial n Q =>
    rw [component_monomial]
    simp only [Polynomial.evalEval, Polynomial.eval_monomial, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C]
    rw [project_evaluation]
    have he := ell.map_smul (y ^ n) (Q.eval (algebraMap K L x))
    simpa [Algebra.smul_def, mul_comm] using he.symm

theorem component_degree (ell : L →ₗ[K] K) (P : L[X][X]) :
    PlaneCurvePointCount.degree (component ell P) ≤ PlaneCurvePointCount.degree P := by
  apply Finset.sup_le
  intro i hi
  have he : (component ell P).coeff i = project ell (P.coeff i) := rfl
  have hrow : P.coeff i ≠ 0 := by
    intro hz
    have hn := Polynomial.mem_support_iff.mp hi
    apply hn
    ext j
    simp only [component_coefficient, hz, Polynomial.coeff_zero, map_zero]
  have hd := Finset.le_sup (f := fun i ↦ i + (P.coeff i).natDegree) (Polynomial.mem_support_iff.mpr hrow)
  have hn : ((component ell P).coeff i).natDegree ≤ (P.coeff i).natDegree := by
    rw [he]
    exact project_degree_le ell _
  exact (Nat.add_le_add_left hn i).trans hd

theorem components_vanish (ell : L →ₗ[K] K) (P : L[X][X]) (x y : K)
    (hz : P.evalEval (algebraMap K L x) (algebraMap K L y) = 0) :
    (component ell P).evalEval x y = 0 := by
  rw [component_evaluation, hz, map_zero]

theorem exists_nonzero_component (P : L[X][X]) (hP : P ≠ 0) :
    ∃ ell : L →ₗ[K] K, component ell P ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis K L
  by_contra h
  have hall (i : Module.Free.ChooseBasisIndex K L) : component
      (FiniteBivariateScalarDecomposition.coordinate b i) P = 0 := by
    by_contra hn
    exact h ⟨_, hn⟩
  apply hP
  rw [← FiniteBivariateScalarDecomposition.reconstruction b P]
  apply Finset.sum_eq_zero
  intro i _
  rw [hall i]
  simp only [extend, Polynomial.map_zero, mul_zero]

end PaperP1.ScalarComponentPoints
