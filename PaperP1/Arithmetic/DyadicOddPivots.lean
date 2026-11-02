module

public import PaperP1.Arithmetic.ReciprocalOddPivots
public import Mathlib.Data.Nat.Log

/-! # An exact finite dyadic transfer for reciprocal odd-valuation pivots -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicOddPivots

open Finset PaperP1.OddPrimePivot PaperP1.ReciprocalOddPivots
open PaperP1.DefectivePredicate PaperP1.DefectCounting

theorem cutoff_mul_two_pow_iff (j n Y : ℕ) (hn : n ≠ 0) (hY : 2 ≤ Y) :
    largestOddPrime (2 ^ j * n) ≤ Y ↔ largestOddPrime n ≤ Y := by
  rw [largestOddPrime_le_iff (by omega), largestOddPrime_le_iff (by omega),
    hDefective_iff_even_factorization, hDefective_iff_even_factorization]
  have hf (p : ℕ) (hpY : Y < p) : (2 ^ j * n).factorization p = n.factorization p := by
    rw [Nat.factorization_mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hn,
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_lt (by omega : 2 < p)]
    simp
  constructor <;> intro h p hp hpY
  · simpa only [hf p hpY] using h p hp hpY
  · rw [hf p hpY]
    exact h p hp hpY

theorem pivot_mul_two_pow (j n : ℕ) (hn : n ≠ 0) (hpivot : 2 < largestOddPrime n) :
    largestOddPrime (2 ^ j * n) = largestOddPrime n := by
  have hupper : largestOddPrime (2 ^ j * n) ≤ largestOddPrime n :=
    (cutoff_mul_two_pow_iff j n (largestOddPrime n) hn (by omega)).mpr le_rfl
  have hnew : 2 < largestOddPrime (2 ^ j * n) := by
    by_contra h
    have hsmall := (cutoff_mul_two_pow_iff j n 2 hn le_rfl).mp (by omega)
    omega
  exact le_antisymm hupper
    ((cutoff_mul_two_pow_iff j n (largestOddPrime (2 ^ j * n)) hn (by omega)).mp le_rfl)

theorem exists_doubling (N n : ℕ) : ∃ j : ℕ, N ≤ 2 ^ j * max 1 n := by
  refine ⟨Nat.clog 2 N, (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) N).trans ?_⟩
  exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _))

def doublingExponent (N n : ℕ) : ℕ := Nat.find (exists_doubling N n)

def dyadicImage (N n : ℕ) : ℕ := 2 ^ doublingExponent N n * n

theorem doublingExponent_le (N n : ℕ) : doublingExponent N n ≤ Nat.clog 2 N := by
  apply Nat.find_min'
  exact (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) N).trans
    (Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)))

theorem dyadicImage_mem {N n : ℕ} (hN : 0 < N) (hn : n ∈ Icc 1 N) :
    dyadicImage N n ∈ Ico N (2 * N) := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hmax : max 1 n = n := max_eq_right hn1
  have hlo := Nat.find_spec (exists_doubling N n)
  change N ≤ 2 ^ doublingExponent N n * max 1 n at hlo
  rw [hmax] at hlo
  refine mem_Ico.mpr ⟨hlo, ?_⟩
  have hmin (j : ℕ) (hj : j < doublingExponent N n) : 2 ^ j * n < N := by
    have h := Nat.find_min (exists_doubling N n) hj
    change ¬ N ≤ 2 ^ j * max 1 n at h
    rw [hmax] at h
    omega
  unfold dyadicImage
  cases he : doublingExponent N n with
  | zero => simp only [pow_zero, one_mul]; omega
  | succ j =>
    have hj := hmin j (by omega)
    rw [pow_succ]
    nlinarith

theorem dyadicImage_pivot {N n : ℕ} (hn : 0 < n) (hpivot : 2 < largestOddPrime n) :
    largestOddPrime (dyadicImage N n) = largestOddPrime n :=
  pivot_mul_two_pow _ _ hn.ne' hpivot

def largePivotValues (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n ↦ 2 < largestOddPrime n

def dyadicSum (N : ℕ) : ℝ := ∑ n ∈ Ico N (2 * N), 1 / (largestOddPrime n : ℝ)

/-- The pair (doubling exponent, image) remembers the original positive integer. -/
theorem dyadic_map_injective_on (N : ℕ) :
    Set.InjOn (fun n ↦ (doublingExponent N n, dyadicImage N n)) (largePivotValues N) := by
  intro n _ m _ h
  have he := congrArg Prod.fst h
  change doublingExponent N n = doublingExponent N m at he
  have hi := congrArg Prod.snd h
  dsimp only [dyadicImage] at hi
  rw [he] at hi
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) _) hi

theorem large_pivot_dyadic_bound (N : ℕ) (hN : 0 < N) :
    (∑ n ∈ largePivotValues N, 1 / (largestOddPrime n : ℝ)) ≤
      (Nat.clog 2 N + 1 : ℕ) * dyadicSum N := by
  calc
    _ ≤ ∑ z ∈ (range (Nat.clog 2 N + 1)) ×ˢ Ico N (2 * N),
        1 / (largestOddPrime z.2 : ℝ) := by
      apply Finset.sum_le_sum_of_injOn
        (fun n ↦ (doublingExponent N n, dyadicImage N n)) (dyadic_map_injective_on N)
      · intro z hz
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
        refine mem_product.mpr ⟨mem_range.mpr (by have := doublingExponent_le N n; omega), ?_⟩
        exact dyadicImage_mem hN (mem_filter.mp hn).1
      · intro n hn
        have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
        rw [dyadicImage_pivot (by omega : 0 < n) (mem_filter.mp hn).2]
      · intro _ _ _
        positivity
    _ = _ := by rw [sum_product]; simp only [dyadicSum, sum_const, card_range, nsmul_eq_mul]

theorem small_pivot_bound (N : ℕ) :
    (∑ n ∈ pivotValues N 2, 1 / (largestOddPrime n : ℝ)) ≤ 2 * (Nat.sqrt N + 1) := by
  have hcard := pivot_count_elementary N 2 (by decide)
  have hprimes : smallPrimesUpTo 2 = {2} := by decide
  rw [hprimes, card_singleton] at hcard
  calc
    _ ≤ ∑ _n ∈ pivotValues N 2, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      simpa only [one_div_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by exact_mod_cast largestOddPrime_pos n : (1 : ℝ) ≤ largestOddPrime n))
    _ = (pivotValues N 2).card := by simp
    _ ≤ _ := by
      exact_mod_cast (by simpa only [pow_one, Nat.mul_comm] using hcard :
        (pivotValues N 2).card ≤ 2 * (Nat.sqrt N + 1))

/-- Explicit finite form of the source's logarithmic-preimage argument. -/
theorem full_dyadic_lower_transfer (N : ℕ) (hN : 0 < N) :
    pivotSum N ≤ 2 * (Nat.sqrt N + 1) + (Nat.clog 2 N + 1 : ℕ) * dyadicSum N := by
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N)
    (fun n ↦ largestOddPrime n ≤ 2) (fun n ↦ 1 / (largestOddPrime n : ℝ))
  have hsplit' : pivotSum N =
      (∑ n ∈ pivotValues N 2, 1 / (largestOddPrime n : ℝ)) +
      ∑ n ∈ largePivotValues N, 1 / (largestOddPrime n : ℝ) := by
    simpa only [pivotSum, pivotValues, largePivotValues, not_le] using hsplit.symm
  rw [hsplit']
  exact add_le_add (small_pivot_bound N) (large_pivot_dyadic_bound N hN)

theorem dyadic_upper_transfer (N : ℕ) (hN : 0 < N) : dyadicSum N ≤ pivotSum (2 * N) := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨hNn, hn2N⟩ := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨hN.trans_le hNn, hn2N.le⟩
  · intro _ _ _
    positivity

end PaperP1.DyadicOddPivots
