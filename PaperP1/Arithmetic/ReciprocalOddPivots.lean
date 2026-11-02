module

public import PaperP1.Arithmetic.OddPrimePivot
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Positive square-part reduction of the actual reciprocal pivot sum

These are finite inequalities for the literal prime-valuation pivots.
No prime-number theorem or reciprocal-prime asymptotic is an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalOddPivots

open Finset PaperP1.OddPrimePivot PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate
open PaperP1.SquarefreeKernelProducts

def pivotSum (X : ℕ) : ℝ := ∑ n ∈ Icc 1 X, 1 / (largestOddPrime n : ℝ)

def primeSum (X : ℕ) : ℝ := ∑ n ∈ Icc 1 X, 1 / (largestPrimeFactor n : ℝ)

theorem pivotSum_nonneg (X : ℕ) : 0 ≤ pivotSum X :=
  sum_nonneg (fun _ _ ↦ by positivity)

theorem primeSum_nonneg (X : ℕ) : 0 ≤ primeSum X :=
  sum_nonneg (fun _ _ ↦ by positivity)

theorem primeSum_le_pivotSum (X : ℕ) : primeSum X ≤ pivotSum X := by
  apply sum_le_sum
  intro n _
  exact one_div_le_one_div_of_le
    (by exact_mod_cast largestOddPrime_pos n) (by exact_mod_cast largestOddPrime_le_largestPrimeFactor n)

theorem primeSum_le (X : ℕ) : primeSum X ≤ X := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 X, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      simpa only [one_div_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by exact_mod_cast largestPrimeFactor_pos n : (1 : ℝ) ≤ largestPrimeFactor n))
    _ = X := by simp

def decomposition (n : ℕ) : Σ _a : ℕ, ℕ :=
  ⟨canonicalSquarePart n, squarefreeKernel n⟩

theorem reconstruction (n : ℕ) (hn : n ≠ 0) :
    (decomposition n).2 * (decomposition n).1 ^ 2 = n :=
  squarefreeKernel_mul_squarePart hn

theorem decomposition_injective_on (X : ℕ) :
    Set.InjOn decomposition (Icc 1 X : Finset ℕ) := by
  intro n hn m hm h
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
  have hh := congrArg (fun z : Σ _a : ℕ, ℕ ↦ z.2 * z.1 ^ 2) h
  simpa only [reconstruction n hn0, reconstruction m hm0] using hh

theorem decomposition_mem {X n : ℕ} (hn : n ∈ Icc 1 X) :
    decomposition n ∈ (Icc 1 (Nat.sqrt X)).sigma (fun a ↦ Icc 1 (X / a ^ 2)) := by
  obtain ⟨hn1, hnX⟩ := mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  have ha : 0 < canonicalSquarePart n := Nat.pos_of_ne_zero (canonical_part_ne_zero n hn0)
  have hk : 0 < squarefreeKernel n := squarefreeKernel_pos n
  have hsquare : canonicalSquarePart n ^ 2 ≤ X := by
    calc
      _ = 1 * canonicalSquarePart n ^ 2 := (one_mul _).symm
      _ ≤ squarefreeKernel n * canonicalSquarePart n ^ 2 :=
        Nat.mul_le_mul_right _ hk
      _ = n := squarefreeKernel_mul_squarePart hn0
      _ ≤ X := hnX
  rw [mem_sigma]
  refine ⟨mem_Icc.mpr ⟨ha, Nat.le_sqrt'.mpr hsquare⟩, mem_Icc.mpr ⟨hk, ?_⟩⟩
  exact (Nat.le_div_iff_mul_le (pow_pos ha 2)).mpr
    ((squarefreeKernel_mul_squarePart hn0).le.trans hnX)

/-- The canonical map is injective; summing over all squarefree candidates
can therefore be enlarged to all positive candidates without a multiplicity loss. -/
theorem square_part_reduction (X : ℕ) :
    pivotSum X ≤ ∑ a ∈ Icc 1 (Nat.sqrt X), primeSum (X / a ^ 2) := by
  unfold pivotSum primeSum
  rw [Finset.sum_sigma']
  apply Finset.sum_le_sum_of_injOn decomposition (decomposition_injective_on X)
  · intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    exact decomposition_mem hn
  · intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    exact le_of_eq (by rw [squarefree_interpretation n hn0]; rfl)
  · intro _ _ _
    positivity

end PaperP1.ReciprocalOddPivots
