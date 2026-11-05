module

public import PaperP1.Algebra.WeightedPolynomialDeterminantDegree
public import PaperP1.Arithmetic.PlaneCurvePointCount
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic.Linarith

/-! # A sharp total-degree product bound for the actual bivariate resultant

The Sylvester rows retain their exponent shifts. No irreducibility, domain,
nonvanishing resultant, or full-degree leading coefficient is required.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateResultantDegree

open Polynomial Finset

variable {R : Type*} [CommRing R]

theorem coefficient_row_degree (P : R[X][X]) (i : ℕ) (hi : P.coeff i ≠ 0) :
    i + (P.coeff i).natDegree ≤ PlaneCurvePointCount.degree P := by
  exact Finset.le_sup (f := fun j ↦ j + (P.coeff j).natDegree) (mem_support_iff.mpr hi)

theorem outer_degree_le (P : R[X][X]) : P.natDegree ≤ PlaneCurvePointCount.degree P := by
  by_cases hp : P = 0
  · simp [hp, PlaneCurvePointCount.degree]
  · have hc : P.coeff P.natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    exact (Nat.le_add_right _ _).trans (coefficient_row_degree P _ hc)

theorem sylvester_budget (m n D E : ℕ) (hm : m ≤ D) (hn : n ≤ E) :
    (∑ j : Fin (m + n), Fin.addCases (fun j : Fin m ↦ (E : ℤ) + j.val)
      (fun j : Fin n ↦ (D : ℤ) + j.val) j) ≤
      ((D * E : ℕ) : ℤ) + ∑ i : Fin (m + n), (i.val : ℤ) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add (fun i : Fin (m + n) ↦ (i.val : ℤ))]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd,
    Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmz : (m : ℤ) ≤ D := by exact_mod_cast hm
  have hnz : (n : ℤ) ≤ E := by exact_mod_cast hn
  have hnonneg := mul_nonneg (sub_nonneg.mpr hmz) (sub_nonneg.mpr hnz)
  nlinarith

theorem sylvester_entry_degree (P Q : R[X][X]) (m n D E : ℕ)
    (hP : PlaneCurvePointCount.degree P ≤ D) (hQ : PlaneCurvePointCount.degree Q ≤ E)
    (i j : Fin (m + n)) (hij : sylvester P Q m n i j ≠ 0) :
    ((sylvester P Q m n i j).natDegree : ℤ) + i.val ≤
      Fin.addCases (fun j : Fin m ↦ (E : ℤ) + j.val)
        (fun j : Fin n ↦ (D : ℤ) + j.val) j := by
  revert hij
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs with hi
    · intro hne
      have hd := (coefficient_row_degree Q (i.val - j.val) hne).trans hQ
      have hle : j.val ≤ i.val := hi.1
      omega
    · intro hne
      exact False.elim (hne rfl)
  · simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs with hi
    · intro hne
      have hd := (coefficient_row_degree P (i.val - j.val) hne).trans hP
      have hle : j.val ≤ i.val := hi.1
      omega
    · intro hne
      exact False.elim (hne rfl)

theorem resultant_degree (P Q : R[X][X]) (D E : ℕ)
    (hP : PlaneCurvePointCount.degree P ≤ D) (hQ : PlaneCurvePointCount.degree Q ≤ E) :
    (P.resultant Q).natDegree ≤ D * E := by
  have hm := (outer_degree_le P).trans hP
  have hn := (outer_degree_le Q).trans hQ
  exact WeightedPolynomialDeterminantDegree.determinant_degree
    (sylvester P Q P.natDegree Q.natDegree) (fun i ↦ (i.val : ℤ))
    (Fin.addCases (fun j : Fin P.natDegree ↦ (E : ℤ) + j.val)
      (fun j : Fin Q.natDegree ↦ (D : ℤ) + j.val)) (D * E)
    (sylvester_budget _ _ _ _ hm hn) (sylvester_entry_degree P Q _ _ D E hP hQ)

end PaperP1.BivariateResultantDegree
