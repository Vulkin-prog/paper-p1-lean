module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

/-! # A literal finite symmetric nonnegative kernel is controlled by its row sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSymmetricKernelBudget
open Finset
open scoped Classical

theorem symmetric_bound {ι : Type*} (S : Finset ι) (x : ι → ℝ) (k : ι → ι → ℝ) (L : ℝ)
    (hk : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ k i j)
    (hsym : ∀ i ∈ S, ∀ j ∈ S, k i j = k j i)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, k i j) ≤ L) :
    (∑ i ∈ S, ∑ j ∈ S, k i j * x i * x j) ≤ L * ∑ i ∈ S, x i ^ 2 := by
  have hrows : (∑ i ∈ S, ∑ j ∈ S, k i j * x i ^ 2) ≤ L * ∑ i ∈ S, x i ^ 2 := by
    calc
      _ = ∑ i ∈ S, (∑ j ∈ S, k i j) * x i ^ 2 := by simp only [sum_mul]
      _ ≤ ∑ i ∈ S, L * x i ^ 2 := sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _))
      _ = _ := by rw [mul_sum]
  have hcols : (∑ i ∈ S, ∑ j ∈ S, k i j * x j ^ 2) ≤ L * ∑ i ∈ S, x i ^ 2 := by
    rw [sum_comm]
    convert hrows using 1
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have hpoint : (∑ i ∈ S, ∑ j ∈ S, 2 * (k i j * x i * x j)) ≤
      ∑ i ∈ S, ∑ j ∈ S, (k i j * x i ^ 2 + k i j * x j ^ 2) := by
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    have hh := mul_nonneg (hk i hi j hj) (sq_nonneg (x i - x j))
    nlinarith
  simp only [← mul_sum, sum_add_distrib] at hpoint
  linarith
end FiniteSymmetricKernelBudget
