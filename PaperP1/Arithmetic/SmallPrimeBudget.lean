module

public import PaperP1.Arithmetic.LargeOddKernel
public import PaperP1.Combinatorics.IntervalMultiples
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # A position-uniform logarithmic budget for small odd prime factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallPrimeBudget

open Finset DefectCounting DefectivePredicate LargeOddKernel

def smallOddSupport (B n : ℕ) : Finset ℕ := (oddPrimeSupport n).filter (· ≤ B)

def smallOddPart (B n : ℕ) : ℕ := (smallOddSupport B n).prod id

def squarefreeKernel (n : ℕ) : ℕ := (oddPrimeSupport n).prod id

theorem smallOddSupport_subset (B n : ℕ) : smallOddSupport B n ⊆ smallPrimesUpTo B := by
  intro p hp
  obtain ⟨hs, hB⟩ := mem_filter.mp hp
  exact mem_smallPrimesUpTo.mpr ⟨prime_of_mem_oddPrimeSupport hs, hB⟩

theorem smallOddPart_pos (B n : ℕ) : 0 < smallOddPart B n := by
  apply prod_pos
  intro p hp
  exact (mem_smallPrimesUpTo.mp (smallOddSupport_subset B n hp)).1.pos

theorem largeOddKernel_pos (B n : ℕ) : 0 < largeOddKernel B n := by
  apply prod_pos
  intro p hp
  exact (prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1).pos

theorem small_mul_large (B n : ℕ) :
    smallOddPart B n * largeOddKernel B n = squarefreeKernel n := by
  unfold smallOddPart smallOddSupport largeOddKernel squarefreeKernel
  convert prod_filter_mul_prod_filter_not (oddPrimeSupport n) (fun p ↦ p ≤ B) id using 1
  simp only [not_le]

theorem smallOddPart_eq_div (B n : ℕ) :
    smallOddPart B n = squarefreeKernel n / largeOddKernel B n := by
  rw [← small_mul_large B n, Nat.mul_div_cancel _ (largeOddKernel_pos B n)]

theorem squarefreeKernel_mul_squarePart {n : ℕ} (hn : n ≠ 0) :
    squarefreeKernel n * canonicalSquarePart n ^ 2 = n :=
  (canonical_odd_mul_sq_decomposition hn).symm

theorem log_smallOddPart (B n : ℕ) :
    Real.log (smallOddPart B n : ℝ) = ∑ p ∈ smallOddSupport B n, Real.log p := by
  unfold smallOddPart
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p hp ↦ by
    exact_mod_cast (mem_smallPrimesUpTo.mp (smallOddSupport_subset B n hp)).1.ne_zero)

theorem log_smallOddPart_nonneg (B n : ℕ) : 0 ≤ Real.log (smallOddPart B n : ℝ) :=
  Real.log_nonneg (by exact_mod_cast smallOddPart_pos B n)

theorem log_smallOddPart_le (B n : ℕ) :
    Real.log (smallOddPart B n : ℝ) ≤
      ∑ p ∈ smallPrimesUpTo B, if p ∣ n then Real.log p else 0 := by
  rw [log_smallOddPart]
  calc
    _ = ∑ p ∈ smallOddSupport B n, if p ∣ n then Real.log p else 0 := by
      apply sum_congr rfl
      intro p hp
      have hs : p ∈ oddPrimeSupport n := (mem_filter.mp hp).1
      have hf : n.factorization p ≠ 0 := by
        have h := Finsupp.mem_support_iff.mp hs
        simp only [oddFactorization, Finsupp.mapRange_apply] at h
        intro hz
        exact h (by rw [hz]; decide)
      rw [ite_eq_left (Nat.dvd_of_factorization_pos hf)]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (smallOddSupport_subset B n)
      intro p hp _
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by
        exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.one_lt.le)
      split_ifs <;> positivity

theorem div_le_factorization_factorial (B p : ℕ) (hp : p.Prime) :
    B / p ≤ B.factorial.factorization p := by
  calc
    _ = ∑ i ∈ range B, if p ∣ i + 1 then 1 else 0 := by
      rw [← Nat.card_multiples B p]
      simp only [card_eq_sum_ones, sum_filter]
    _ ≤ ∑ i ∈ range B, (i + 1).factorization p := by
      apply sum_le_sum
      intro i _
      split_ifs with hi
      · exact hp.factorization_pos_of_dvd (by omega) hi
      · exact Nat.zero_le _
    _ = _ := by
      rw [Nat.factorial_eq_prod_range_add_one]
      exact (Nat.factorization_prod_apply (fun i _ ↦ by omega)).symm

theorem sum_div_mul_log_le_log_factorial (B : ℕ) :
    (∑ p ∈ smallPrimesUpTo B, (B / p : ℕ) * Real.log p) ≤ Real.log (B.factorial : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  have hsupport : B.factorial.factorization.support ⊆ smallPrimesUpTo B := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact mem_smallPrimesUpTo.mpr ⟨hprime,
      hprime.dvd_factorial.mp (Nat.dvd_of_factorization_pos (Finsupp.mem_support_iff.mp hp))⟩
  rw [Finsupp.sum_of_support_subset _ hsupport _ (by simp)]
  apply sum_le_sum
  intro p hp
  have hpprime := (mem_smallPrimesUpTo.mp hp).1
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast div_le_factorization_factorial B p hpprime)
    (Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le))

theorem prime_log_sum_le (B : ℕ) :
    (∑ p ∈ smallPrimesUpTo B, Real.log p) ≤ (B : ℝ) * Real.log 4 := by
  have hprod : (primorial B : ℝ) = ∏ p ∈ smallPrimesUpTo B, (p : ℝ) := by
    simp [primorial, smallPrimesUpTo, Nat.cast_prod]
  have hlog : Real.log (primorial B : ℝ) = ∑ p ∈ smallPrimesUpTo B, Real.log p := by
    rw [hprod, Real.log_prod]
    intro p hp
    exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.ne_zero
  rw [← hlog]
  have hbound : (primorial B : ℝ) ≤ (4 : ℝ) ^ B := by exact_mod_cast primorial_le_four_pow B
  simpa only [Real.log_pow] using Real.log_le_log (by exact_mod_cast primorial_pos B) hbound

theorem log_factorial_le (B : ℕ) :
    Real.log (B.factorial : ℝ) ≤ (B : ℝ) * Real.log B := by
  have hb : (B.factorial : ℝ) ≤ (B : ℝ) ^ B := by exact_mod_cast Nat.factorial_le_pow B
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hb

theorem interval_log_budget_exact (U B : ℕ) :
    (∑ n ∈ Ico U (U + B), Real.log (smallOddPart B n : ℝ)) ≤
      Real.log (B.factorial : ℝ) + ∑ p ∈ smallPrimesUpTo B, Real.log p := by
  calc
    _ ≤ ∑ n ∈ Ico U (U + B),
        ∑ p ∈ smallPrimesUpTo B, if p ∣ n then Real.log p else 0 :=
      sum_le_sum fun n _ ↦ log_smallOddPart_le B n
    _ = ∑ p ∈ smallPrimesUpTo B,
        (((Ico U (U + B)).filter fun n ↦ p ∣ n).card : ℝ) * Real.log p := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ smallPrimesUpTo B, ((B / p : ℕ) + 1) * Real.log p := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast IntervalMultiples.card_multiples_interval_le U B p
      · exact Real.log_nonneg (by exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.one_lt.le)
    _ = (∑ p ∈ smallPrimesUpTo B, (B / p : ℕ) * Real.log p) +
        ∑ p ∈ smallPrimesUpTo B, Real.log p := by simp [add_mul, sum_add_distrib]
    _ ≤ _ := add_le_add (sum_div_mul_log_le_log_factorial B) le_rfl

theorem interval_log_budget (U B : ℕ) :
    (∑ n ∈ Ico U (U + B), Real.log (smallOddPart B n : ℝ)) ≤
      (B : ℝ) * Real.log B + (B : ℝ) * Real.log 4 := by
  exact (interval_log_budget_exact U B).trans
    (add_le_add (log_factorial_le B) (prime_log_sum_le B))

def largeSmallPartValues (U B : ℕ) (A : ℝ) : Finset ℕ :=
  (Ico U (U + B)).filter fun n ↦ (B : ℝ) ^ A < (smallOddPart B n : ℝ)

theorem card_largeSmallPartValues_le (U B : ℕ) (hB : 2 ≤ B) (A : ℝ) (hA : 0 < A) :
    ((largeSmallPartValues U B A).card : ℝ) ≤
      (A⁻¹ + Real.log 4 / (A * Real.log B)) * B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hlarge (n : ℕ) (hn : n ∈ largeSmallPartValues U B A) :
      A * Real.log B ≤ Real.log (smallOddPart B n : ℝ) := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hBpos A) (mem_filter.mp hn).2
    rw [Real.log_rpow hBpos A] at h
    exact h.le
  have hsum : ((largeSmallPartValues U B A).card : ℝ) * (A * Real.log B) ≤
      (B : ℝ) * Real.log B + (B : ℝ) * Real.log 4 := by
    calc
      _ = ∑ n ∈ largeSmallPartValues U B A, A * Real.log B := by
        simp only [sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ largeSmallPartValues U B A, Real.log (smallOddPart B n : ℝ) :=
        sum_le_sum hlarge
      _ ≤ ∑ n ∈ Ico U (U + B), Real.log (smallOddPart B n : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro n _ _
        exact log_smallOddPart_nonneg B n
      _ ≤ _ := interval_log_budget U B
  calc
    _ ≤ ((B : ℝ) * Real.log B + (B : ℝ) * Real.log 4) / (A * Real.log B) :=
      (le_div_iff₀ (mul_pos hA hlogB)).mpr hsum
    _ = _ := by field_simp

/-- The source's two estimates, with a fixed explicit absolute remainder. -/
theorem companion_T2_1 (U B : ℕ) (hB : 2 ≤ B) :
    (∑ n ∈ Ico U (U + B), Real.log (smallOddPart B n : ℝ)) ≤
        (B : ℝ) * Real.log B + Real.log 4 * B ∧
      ∀ A : ℝ, 0 < A → ((largeSmallPartValues U B A).card : ℝ) ≤
        (A⁻¹ + (Real.log 4 / A) / Real.log B) * B := by
  constructor
  · simpa only [mul_comm (Real.log 4) (B : ℝ)] using interval_log_budget U B
  · intro A hA
    simpa only [div_div, mul_comm (Real.log B) A] using card_largeSmallPartValues_le U B hB A hA

end PaperP1.SmallPrimeBudget
