module

public import PaperP1.Arithmetic.OldValuePrimeBudget
public import PaperP1.Arithmetic.PrimeSetEuler

/-! # The exact rounded old-prime cardinality budget in fixed-window branching -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OldPrimeCardinality

open Finset PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.LocalDefectBound
  PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget

def largeOld (R : Finset ℕ) (B : ℕ) : Finset ℕ := (oldPrimes R).filter (B < ·)

def primeCountBudget (N L j : ℕ) : ℕ :=
  ⌈(primeCount (L + 1) : ℝ) + (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) / Real.log (L + 1)⌉₊

theorem primePool_eq_union (R : Finset ℕ) (B : ℕ) : primePool R B = smallPrimesUpTo B ∪ largeOld R B := by
  ext p
  constructor
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · exact mem_union_left _ hp
    · by_cases hBp : B < p
      · exact mem_union_right _ (mem_filter.mpr ⟨hp, hBp⟩)
      · exact mem_union_left _ (mem_smallPrimesUpTo.mpr ⟨primePool_prime R B p (mem_union_right _ hp), by omega⟩)
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · exact mem_union_left _ hp
    · exact mem_union_right _ (mem_filter.mp hp).1

theorem primePool_card (R : Finset ℕ) (B : ℕ) :
    (primePool R B).card = primeCount B + (largeOld R B).card := by
  rw [primePool_eq_union, card_union_of_disjoint]
  · rfl
  · apply disjoint_left.mpr
    intro p hp hq
    have h := (mem_smallPrimesUpTo.mp hp).2
    have h' := (mem_filter.mp hq).2
    omega

theorem largeOld_card_log_le (R : Finset ℕ) (B : ℕ) (hR : ∀ n ∈ R, 0 < n) :
    (largeOld R B).card * Real.log B ≤ ∑ n ∈ R, Real.log n := by
  calc
    _ = ∑ _p ∈ largeOld R B, Real.log B := by simp
    _ ≤ ∑ p ∈ largeOld R B, Real.log p := by
      apply sum_le_sum
      intro p hp
      have hBp := (mem_filter.mp hp).2
      by_cases hB : B = 0
      · simp only [hB, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg p
      · exact Real.log_le_log (by exact_mod_cast (show 0 < B by omega)) (by exact_mod_cast hBp.le)
    _ ≤ ∑ p ∈ oldPrimes R, Real.log p :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ ↦ Real.log_natCast_nonneg p)
    _ ≤ _ := oldPrimes_log_sum_le R hR

theorem raw_pool_card_le {A : Finset ℕ} {N L j : ℕ} (hA : A ⊆ Model.dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N) (hj : A.card ≤ j) :
    (primePool (rawValues A L) (L + 1)).card ≤ primeCountBudget N L j := by
  let R := rawValues A L
  have hR : ∀ n ∈ R, 1 ≤ n ∧ n ≤ 3 * N := fun n hn ↦ rawValues_bounds hA hN hLN hn
  have hlarge := largeOld_card_log_le R (L + 1) (fun n hn ↦ by have h := (hR n hn).1; omega)
  have hvalues : (∑ n ∈ R, Real.log n) ≤ R.card * Real.log (3 * N : ℕ) := by
    calc
      _ ≤ ∑ _n ∈ R, Real.log (3 * N : ℕ) := sum_le_sum fun n hn ↦
        Real.log_le_log (by exact_mod_cast (show 0 < n by have h := (hR n hn).1; omega))
          (by exact_mod_cast (hR n hn).2)
      _ = _ := by simp
  have hRcard := (rawValues_card_le A L (fun x hx ↦ by have h := (mem_Ico.mp (hA hx)).1; omega)).trans
    (Nat.mul_le_mul_right (L + 1) hj)
  have hRcardR : (R.card : ℝ) ≤ (j : ℝ) * (L + 1) := by exact_mod_cast hRcard
  have hprod := (hlarge.trans hvalues).trans
    (mul_le_mul_of_nonneg_right hRcardR (Real.log_natCast_nonneg (3 * N)))
  have hlog : 0 < Real.log (L + 1) := Real.log_pos (by
    have h : (0 : ℝ) < L := by exact_mod_cast hL
    linarith)
  simp only [Nat.cast_add, Nat.cast_one] at hprod
  have hdiv := (le_div_iff₀ hlog).mpr hprod
  have hreal : ((primePool R (L + 1)).card : ℝ) ≤
      (primeCount (L + 1) : ℝ) + (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) / Real.log (L + 1) := by
    rw [primePool_card, Nat.cast_add]
    linarith
  change (primePool R (L + 1)).card ≤
    ⌈(primeCount (L + 1) : ℝ) + (j : ℝ) * (L + 1) * Real.log (3 * N : ℕ) / Real.log (L + 1)⌉₊
  exact Nat.cast_le.mp (hreal.trans (Nat.le_ceil _))

end PaperP1.OldPrimeCardinality
