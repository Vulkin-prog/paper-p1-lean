module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.Fin

/-! # Actual derivative matrices and their common-factor determinant identity

Leibniz's formula gives a lower triangular multiplication matrix.
Its diagonal is the common factor, so its determinant is an exact power.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnalyticWronskianProduct

open Finset

def jetMatrix (n : ℕ) (f : Fin n → ℝ → ℝ) (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ iteratedDeriv i.val (f j) x

def multiplicationMatrix (n : ℕ) (a : ℝ → ℝ) (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ if j.val ≤ i.val then (i.val.choose j.val : ℝ) * iteratedDeriv (i.val - j.val) a x else 0

def wronskian (n : ℕ) (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ := (jetMatrix n f x).det

theorem sum_initial (n k : ℕ) (hk : k < n) (g : ℕ → ℝ) :
    (∑ j : Fin n, if j.val ≤ k then g j.val else 0) = ∑ j ∈ range (k + 1), g j := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ if j ≤ k then g j else 0)]
  have hsub : range (k + 1) ⊆ range n := range_mono (by omega)
  calc
    _ = ∑ j ∈ range (k + 1), if j ≤ k then g j else 0 := by
      symm
      apply sum_subset hsub
      intro j _hj hj
      have hh : ¬j ≤ k := by simp only [mem_range] at hj; omega
      simp only [hh, ite_false]
    _ = _ := sum_congr rfl (fun j hj ↦ by rw [ite_eq_left (by have := mem_range.mp hj; omega)])

theorem multiplicationMatrix_lower (n : ℕ) (a : ℝ → ℝ) (x : ℝ) :
    (multiplicationMatrix n a x).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  change (if j.val ≤ i.val then _ else _) = 0
  exact ite_eq_right (by omega)

theorem multiplicationMatrix_det (n : ℕ) (a : ℝ → ℝ) (x : ℝ) :
    (multiplicationMatrix n a x).det = a x ^ n := by
  rw [Matrix.det_of_isLowerTriangular _ (multiplicationMatrix_lower n a x)]
  simp only [multiplicationMatrix, le_refl, ite_true, Nat.choose_self, Nat.cast_one,
    Nat.sub_self, iteratedDeriv_zero, one_mul, prod_const, card_univ, Fintype.card_fin]

theorem jetMatrix_product (n : ℕ) (a : ℝ → ℝ) (f : Fin n → ℝ → ℝ) (x : ℝ)
    (ha : ContDiffAt ℝ n a x) (hf : ∀ j, ContDiffAt ℝ n (f j) x) :
    jetMatrix n (fun j t ↦ a t * f j t) x = multiplicationMatrix n a x * jetMatrix n f x := by
  ext i j
  have hd : (i.val : WithTop ℕ∞) ≤ n := by exact_mod_cast i.isLt.le
  change iteratedDeriv i.val (fun t ↦ a t * f j t) x = _
  have he : (fun t ↦ a t * f j t) = (fun t ↦ f j t * a t) := funext (fun _ ↦ mul_comm _ _)
  rw [he, iteratedDeriv_fun_mul ((hf j).of_le hd) (ha.of_le hd), Matrix.mul_apply]
  simp only [multiplicationMatrix, jetMatrix, ite_mul, zero_mul]
  rw [sum_initial n i.val i.isLt (fun k : ℕ ↦
    (i.val.choose k : ℝ) * iteratedDeriv (i.val - k) a x * iteratedDeriv k (f j) x)]
  apply sum_congr rfl
  intro k _hk
  ring

theorem wronskian_product (n : ℕ) (a : ℝ → ℝ) (f : Fin n → ℝ → ℝ) (x : ℝ)
    (ha : ContDiffAt ℝ n a x) (hf : ∀ j, ContDiffAt ℝ n (f j) x) :
    wronskian n (fun j t ↦ a t * f j t) x = a x ^ n * wronskian n f x := by
  change (jetMatrix n (fun j t ↦ a t * f j t) x).det = _
  rw [jetMatrix_product n a f x ha hf, Matrix.det_mul, multiplicationMatrix_det]
  rfl

end PaperP1.AnalyticWronskianProduct
