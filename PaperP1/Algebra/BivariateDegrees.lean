module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Lean.Elab.Tactic.Omega

/-! # Exact partial degrees and coefficients of integer bivariate factors

Mathlib's nested notation has inner variable X and outer variable Y.
Swapping the variables therefore identifies the other partial degree.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateDegrees

open Polynomial

theorem card_support_le_natDegree_add_one {R : Type*} [Semiring R] (p : R[X]) :
    p.support.card ≤ p.natDegree + 1 := by
  have hsub : p.support ⊆ Finset.range (p.natDegree + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (le_natDegree_of_ne_zero (mem_support_iff.mp hi)))
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)

def degreeX (P : ℤ[X][X]) : ℕ := (Bivariate.swap P).natDegree

def degreeY (P : ℤ[X][X]) : ℕ := P.natDegree

theorem coeff_swap (P : ℤ[X][X]) (i j : ℕ) :
    ((Bivariate.swap P).coeff j).coeff i = (P.coeff i).coeff j := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hn : n = i <;> by_cases hm : m = j <;> simp [coeff_monomial, hn, hm]

theorem natDegree_coeff_le_degreeX (P : ℤ[X][X]) (i : ℕ) :
    (P.coeff i).natDegree ≤ degreeX P := by
  by_cases hp : P.coeff i = 0
  · simp only [hp, natDegree_zero]
    exact Nat.zero_le _
  · have hlc : (P.coeff i).coeff (P.coeff i).natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    have hs : (Bivariate.swap P).coeff (P.coeff i).natDegree ≠ 0 := by
      intro hzero
      apply hlc
      rw [← coeff_swap, hzero, coeff_zero]
    exact le_natDegree_of_ne_zero hs

theorem factor_natDegree_le (Q R : ℤ[X][X]) (hQR : Q * R ≠ 0) :
    Q.natDegree ≤ (Q * R).natDegree := by
  rw [natDegree_mul (left_ne_zero_of_mul hQR) (right_ne_zero_of_mul hQR)]
  omega

theorem factor_degreeX_le (Q R : ℤ[X][X]) (hQR : Q * R ≠ 0) : degreeX Q ≤ degreeX (Q * R) := by
  have hs : Bivariate.swap (Q * R) ≠ 0 := by
    intro h
    apply hQR
    exact (Bivariate.swap (R := ℤ)).injective
      (h.trans (map_zero (Bivariate.swap (R := ℤ))).symm)
  have hs' : Bivariate.swap Q * Bivariate.swap R ≠ 0 := by simpa only [map_mul] using hs
  simpa only [degreeX, map_mul] using factor_natDegree_le (Bivariate.swap Q) (Bivariate.swap R) hs'

theorem factor_partial_degrees_le (Q R : ℤ[X][X]) (hQR : Q * R ≠ 0) :
    degreeX Q ≤ degreeX (Q * R) ∧ degreeY Q ≤ degreeY (Q * R) :=
  ⟨factor_degreeX_le Q R hQR, factor_natDegree_le Q R hQR⟩

end PaperP1.BivariateDegrees
