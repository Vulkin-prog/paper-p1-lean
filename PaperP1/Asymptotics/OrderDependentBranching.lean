module

public import PaperP1.Arithmetic.PrimeCardinalityEuler
public import PaperP1.Asymptotics.FixedWindowBranching

/-! # The literal finite order-dependent branching exception

The entire new relative vector remains independent of all old raw values.
The source's rounded prime-cardinality budget is retained, with its
logarithmic Euler gain, and no separate contact deletion is needed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderDependentBranching

open Finset PaperP1.Model PaperP1.OldValuePrimeBudget PaperP1.OldPrimeCardinality
  PaperP1.BranchingExceptional PaperP1.FixedWindowBranching
  PaperP1.ConditionalWindowRank PaperP1.WindowPoolCount

def exponent (N L j : ℕ) : ℝ :=
  PrimeCardinalityEuler.constant * Real.sqrt
    ((primeCountBudget N L j : ℝ) / Real.log ((primeCountBudget N L j : ℝ) + 2))

def exception (N L j : ℕ) : ℝ :=
  ((L + 1 : ℕ) : ℝ) / 2 * Real.sqrt (3 * N : ℕ) * Real.exp (exponent N L j)

def sourceException (N L j : ℕ) : ℝ :=
  (j : ℝ) * (2 * L + 1) +
    ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) * Real.exp (exponent N L j)

theorem exception_nonneg (N L j : ℕ) : 0 ≤ exception N L j := by
  unfold exception
  positivity

theorem exception_le_source (N L j : ℕ) : exception N L j ≤ sourceException N L j := by
  have hp : 0 ≤ ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
      Real.exp (exponent N L j) := by positivity
  have hj : (0 : ℝ) ≤ (j : ℝ) * (2 * L + 1) := by positivity
  unfold exception sourceException
  nlinarith

theorem finite_exception_bound {N L j : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N)
    (hA : A ⊆ dyadicBlock N) (hj : A.card ≤ j) :
    ((badStarts N L (rawValues A L)).card : ℝ) ≤ exception N L j := by
  have hcard := raw_pool_card_le hA hN hL hLN hj
  have hpool := PrimeCardinalityEuler.naturalValues_card_le_sqrt_exp
    (primePool (rawValues A L) (L + 1)) (primePool_prime _ _)
    (primeCountBudget N L j) hcard (3 * N)
  have hhalf := badStarts_card_half (rawValues A L) hN hLN
  have hmul := mul_le_mul_of_nonneg_left hpool
    (by positivity : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2)
  exact hhalf.trans (by simpa only [poolValues, exponent, exception, mul_assoc] using hmul)

/-- The exact finite source conclusion, with the sharper exception bound too.
No fixed-order hypothesis is imposed on the number of exposed windows. -/
theorem finite_independence {N L j : ℕ} {A : Finset ℕ}
    (hN : 2 ≤ N) (hL : 0 < L) (hLN : L ≤ N)
    (hA : A ⊆ dyadicBlock N) (hj : A.card ≤ j) :
    ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ IndependentConclusion N L A E ∧
      (E.card : ℝ) ≤ exception N L j ∧ (E.card : ℝ) ≤ sourceException N L j := by
  have h := finite_exception_bound hN hL hLN hA hj
  exact ⟨badStarts N L (rawValues A L), badStarts_subset _ _ _,
    retained_independent hN hA, h, h.trans (exception_le_source _ _ _)⟩

end PaperP1.OrderDependentBranching
