module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-! # A finite low-order and geometric-tail split for positive weighted leakage sequences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedLeakageCutoff

open Finset

theorem weight_comparison (r K : ℕ) (hKr : K ≤ r) :
    (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ K)⁻¹ * (4 : ℝ) ^ r := by
  have hp : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num) _
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  calc
    _ ≤ (2 : ℝ) ^ r * (2 : ℝ) ^ r := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hKr) (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

theorem finite_split (h : ℕ → ℝ) (hh : ∀ r, 0 ≤ h r) (n K : ℕ) :
    (∑ r ∈ range (n + 1), (2 : ℝ) ^ r * h r) ≤
      (∑ r ∈ range (K + 1), (2 : ℝ) ^ r * h r) +
        ((2 : ℝ) ^ K)⁻¹ * ∑ r ∈ range (n + 1), (4 : ℝ) ^ r * h r := by
  let S := range (n + 1)
  have hlow : (∑ r ∈ S.filter (fun r ↦ r ≤ K), (2 : ℝ) ^ r * h r) ≤
      ∑ r ∈ range (K + 1), (2 : ℝ) ^ r * h r := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro r hr
      exact mem_range.mpr (by have h := (mem_filter.mp hr).2; omega)
    · intro r _hr _hn
      exact mul_nonneg (by positivity) (hh r)
  have hhigh : (∑ r ∈ S.filter (fun r ↦ ¬r ≤ K), (2 : ℝ) ^ r * h r) ≤
      ((2 : ℝ) ^ K)⁻¹ * ∑ r ∈ S, (4 : ℝ) ^ r * h r := by
    calc
      _ ≤ ∑ r ∈ S.filter (fun r ↦ ¬r ≤ K), (((2 : ℝ) ^ K)⁻¹ * (4 : ℝ) ^ r) * h r :=
        sum_le_sum fun r hr ↦ mul_le_mul_of_nonneg_right
          (weight_comparison r K (by have h := (mem_filter.mp hr).2; omega)) (hh r)
      _ = ((2 : ℝ) ^ K)⁻¹ * ∑ r ∈ S.filter (fun r ↦ ¬r ≤ K), (4 : ℝ) ^ r * h r := by
        rw [mul_sum]
        apply sum_congr rfl
        intro r _hr
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun r _hr _hn ↦ mul_nonneg (by positivity) (hh r))) (by positivity)
  have hsplit := sum_filter_add_sum_filter_not S (fun r ↦ r ≤ K) (fun r ↦ (2 : ℝ) ^ r * h r)
  linarith only [hlow, hhigh, hsplit]

end PaperP1.WeightedLeakageCutoff
