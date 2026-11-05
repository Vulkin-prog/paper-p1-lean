module

public import PaperP1.Algebra.PolynomialTangentDegree
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Actual polynomial tangent Wronskians and their degree budgets

The rowwise estimate retains the exact triangular cost of repeated derivatives.
It implies the polynomial degree allowance used in BCN Proposition 5.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialTangentWronskian

open Finset MvPolynomial PolynomialTangentDegree

variable {R : Type*} [CommRing R]

theorem determinant_row_degree {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial σ R)) (d : ι → ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d i) :
    A.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro s _hs
  have hp : (∏ i, A (s i) i).totalDegree ≤ ∑ i, d i := by
    calc
      _ ≤ ∑ i, (A (s i) i).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ i, d (s i) := sum_le_sum (fun i _hi ↦ hA (s i) i)
      _ = _ := Equiv.sum_comp s d
  have hs : (s.sign • ∏ i, A (s i) i).totalDegree ≤ (∏ i, A (s i) i).totalDegree := by
    simpa only [Units.smul_def] using
      (totalDegree_smul_le (s.sign : ℤ) (∏ i, A (s i) i))
  exact hs.trans hp

def wronskian (P : MvPolynomial (Fin 2) R) (n : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  Matrix.det (fun i j : Fin n ↦ (tangent P)^[i.val] (f j))

theorem wronskian_degree_sum (P : MvPolynomial (Fin 2) R) (n k : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) R) (hf : ∀ i, (f i).totalDegree ≤ k) :
    (wronskian P n f).totalDegree ≤ ∑ i : Fin n, (k + i.val * P.totalDegree) := by
  apply determinant_row_degree
  intro i j
  exact (iterate_degree P (f j) i.val).trans (Nat.add_le_add_right (hf j) _)

theorem wronskian_degree (P : MvPolynomial (Fin 2) R) (n k : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) R) (hf : ∀ i, (f i).totalDegree ≤ k) :
    (wronskian P n f).totalDegree ≤ n * (k + n * P.totalDegree) := by
  calc
    _ ≤ ∑ i : Fin n, (k + i.val * P.totalDegree) := wronskian_degree_sum P n k f hf
    _ ≤ ∑ _i : Fin n, (k + n * P.totalDegree) := by
      apply sum_le_sum
      intro i _hi
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt.le) _
    _ = _ := by simp

theorem wronskian_degree_triangular (P : MvPolynomial (Fin 2) R) (n k : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) R) (hf : ∀ i, (f i).totalDegree ≤ k) :
    (wronskian P n f).totalDegree ≤ n * k + (n * (n - 1) / 2) * P.totalDegree := by
  have he : (∑ i : Fin n, (k + i.val * P.totalDegree)) =
      n * k + (n * (n - 1) / 2) * P.totalDegree := by
    rw [sum_add_distrib, ← sum_mul, Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i),
      Finset.sum_range_id]
    simp
  exact (wronskian_degree_sum P n k f hf).trans_eq he

end PaperP1.PolynomialTangentWronskian
