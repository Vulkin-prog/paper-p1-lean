module

public import PaperP1.Arithmetic.OddPrimePivot

/-! # Exact actual odd-valuation pivots of squares and primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OddPivotSpecialValues

open PaperP1.OddPrimePivot PaperP1.DefectivePredicate

theorem square (n : ℕ) : largestOddPrime (n ^ 2) = 1 := by
  rw [largestOddPrime, PaperP1.SquarefreeKernelProducts.support_square, Finset.sup_empty]
  rfl

theorem prime {p : ℕ} (hp : p.Prime) : largestOddPrime p = p := by
  have hs : oddPrimeSupport p = {p} := by
    simp [oddPrimeSupport, oddFactorization, hp.factorization]
  simp only [largestOddPrime, hs, Finset.sup_singleton, id_eq, max_eq_right hp.one_lt.le]

end PaperP1.OddPivotSpecialValues
