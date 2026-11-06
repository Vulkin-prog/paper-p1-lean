module

public import PaperP1.Arithmetic.OrdinarySmoothDyadicDensity
public import PaperP1.Arithmetic.NonanchorPivotSelection
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # The actual ordinary smooth indicator is completely multiplicative and counts every literal finite candidate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySmoothIndicator
open PaperP1 Finset OddPrimePivot OrdinarySmoothCensus NonanchorPivotSelection
open scoped Classical

def value (Y n : ℕ) : ℝ := if n ≠ 0 ∧ largestPrimeFactor n ≤ Y then 1 else 0

@[simp]
theorem value_zero (Y : ℕ) : value Y 0 = 0 := by simp [value]

@[simp]
theorem value_one (Y : ℕ) (hY : 1 ≤ Y) : value Y 1 = 1 := by simp [value, hY]

theorem value_nonneg (Y n : ℕ) : 0 ≤ value Y n := by unfold value; split <;> norm_num

theorem value_le_one (Y n : ℕ) : value Y n ≤ 1 := by unfold value; split <;> norm_num

theorem value_mul (Y m n : ℕ) : value Y (m*n) = value Y m * value Y n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [value, Nat.mul_ne_zero hm hn, largestPrimeFactor_mul hm hn, true_and, hm, hn, ne_eq,
    not_false_eq_true, max_le_iff]
  split_ifs <;> norm_num <;> tauto

def arithmetic (Y : ℕ) : ArithmeticFunction ℝ := ⟨value Y, value_zero Y⟩

theorem isMultiplicative (Y : ℕ) (hY : 1 ≤ Y) : (arithmetic Y).IsMultiplicative := by
  refine ⟨value_one Y hY, ?_⟩
  intro m n _hcoprime
  exact value_mul Y m n

theorem sum_eq_filter_card (Y : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) :
    (∑ n ∈ S, value Y n) = ((S.filter fun n ↦ largestPrimeFactor n ≤ Y).card : ℝ) := by
  simp only [value]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro n hn
  simp [hS n hn]

theorem dyadic_sum (N Y : ℕ) (hN : 0 < N) :
    (∑ n ∈ Ico N (2*N), value Y n) = (OrdinarySmoothDyadicDensity.dyadicSmooth N Y).card := by
  exact sum_eq_filter_card Y _ (fun n hn ↦ by have := (mem_Ico.mp hn).1; omega)

theorem short_sum (j h Y : ℕ) (hj : 0 < j) :
    (∑ r ∈ range h, value Y (j+r)) = (ordinaryIndices j h (Y : ℝ)).card := by
  have he : (range h).filter (fun r ↦ largestPrimeFactor (j+r) ≤ Y) =
      ((ordinaryIndices j h (Y : ℝ)).image fun i ↦ i.val) := by
    ext r
    simp only [mem_filter, mem_range, mem_image, ordinaryIndices, mem_univ, true_and]
    constructor
    · intro hr
      exact ⟨⟨r, hr.1⟩, by exact_mod_cast hr.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.isLt, by exact_mod_cast hi⟩
  have hc := card_image_of_injective (ordinaryIndices j h (Y : ℝ)) Fin.val_injective
  have hs : (∑ r ∈ range h, value Y (j+r)) =
      (((range h).filter (fun r ↦ largestPrimeFactor (j+r) ≤ Y)).card : ℝ) := by
    simp only [value, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro r _hr
    simp [show j ≠ 0 by omega]
  rw [hs, he, hc]
end OrdinarySmoothIndicator
