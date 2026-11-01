module

public import PaperP1.Arithmetic.OldPrimeCardinality
public import PaperP1.Arithmetic.WindowPoolCount

/-! # A deterministic branching exception set with no separate contact deletion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BranchingExceptional

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ConditionalWindowRank
  PaperP1.WindowPoolCount PaperP1.OldValuePrimeBudget PaperP1.OldPrimeCardinality

def badStarts (N L : ℕ) (R : Finset ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ 2 ≤ (supportedIndices R (x - 1) (L + 1)).card

theorem badStarts_subset (N L : ℕ) (R : Finset ℕ) : badStarts N L R ⊆ dyadicBlock N := filter_subset _ _

theorem retained_card_le_one {N L x : ℕ} {R : Finset ℕ} (hx : x ∈ dyadicBlock N)
    (hnot : x ∉ badStarts N L R) : (supportedIndices R (x - 1) (L + 1)).card ≤ 1 := by
  by_contra h
  exact hnot (mem_filter.mpr ⟨hx, by omega⟩)

theorem twice_badStarts_card_le {N L : ℕ} (R : Finset ℕ) (hN : 2 ≤ N) (hL : L ≤ N) :
    2 * (badStarts N L R).card ≤ (L + 1) * (poolValues R (L + 1) (3 * N)).card := by
  calc
    _ = ∑ _x ∈ badStarts N L R, (2 : ℕ) := by simp; omega
    _ ≤ ∑ x ∈ badStarts N L R, (supportedIndices R (x - 1) (L + 1)).card :=
      sum_le_sum fun _ hx ↦ (mem_filter.mp hx).2
    _ ≤ ∑ x ∈ dyadicBlock N, (supportedIndices R (x - 1) (L + 1)).card :=
      sum_le_sum_of_subset_of_nonneg (badStarts_subset N L R) (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ _ := sum_supportedIndices_dyadic hN hL

theorem badStarts_card_half {N L : ℕ} (R : Finset ℕ) (hN : 2 ≤ N) (hL : L ≤ N) :
    ((badStarts N L R).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2 * (poolValues R (L + 1) (3 * N)).card := by
  have h : 2 * ((badStarts N L R).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * (poolValues R (L + 1) (3 * N)).card := by
    exact_mod_cast twice_badStarts_card_le R hN hL
  linarith

theorem badStarts_card_explicit {A : Finset ℕ} {N L j : ℕ} (hA : A ⊆ dyadicBlock N)
    (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N) (hj : A.card ≤ j) :
    ((badStarts N L (rawValues A L)).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) / 2 * Real.sqrt (3 * N : ℕ) * Real.exp (2 * Real.sqrt (primeCountBudget N L j)) := by
  have hhalf := badStarts_card_half (rawValues A L) hN hLN
  have hpool := PrimeSetEuler.naturalValues_card_le_sqrt_exp (primePool (rawValues A L) (L + 1))
    (fun p hp ↦ (primePool_prime _ _ _ hp).one_lt.le) (3 * N)
  have hcard := raw_pool_card_le hA hN hL hLN hj
  have hsqrt := Real.sqrt_le_sqrt (by exact_mod_cast hcard :
    ((primePool (rawValues A L) (L + 1)).card : ℝ) ≤ primeCountBudget N L j)
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hpool' := hpool.trans (mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left hpool' (by positivity : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2)
  exact hhalf.trans (by simpa only [poolValues, mul_assoc] using hmul)

end PaperP1.BranchingExceptional
