module

public import PaperP1.Arithmetic.SmallPrimeBudget
public import Mathlib.NumberTheory.Primorial

/-! # Three canonical parts of a squarefree kernel relative to a fixed source product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeSquarefreeParts

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate PaperP1.DefectCounting
  PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel

def sourceSupport (H n m : ℕ) : Finset ℕ := (oddPrimeSupport n).filter fun p ↦ H < p ∧ p ∣ m

def residualSupport (H n m : ℕ) : Finset ℕ := (oddPrimeSupport n).filter fun p ↦ H < p ∧ ¬p ∣ m

def sourcePart (H n m : ℕ) : ℕ := (sourceSupport H n m).prod id

def residualPart (H n m : ℕ) : ℕ := (residualSupport H n m).prod id

theorem sourcePart_pos (H n m : ℕ) : 0 < sourcePart H n m :=
  prod_pos (fun _ hp ↦ (prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1).pos)

theorem residualPart_pos (H n m : ℕ) : 0 < residualPart H n m :=
  prod_pos (fun _ hp ↦ (prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1).pos)

theorem sourcePart_dvd (H n m : ℕ) : sourcePart H n m ∣ m := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1).prime
  · intro p hp
    exact (mem_filter.mp hp).2.2

theorem smallOddPart_dvd_primorial (H n : ℕ) : smallOddPart H n ∣ primorial H := by
  have heq : primorial H = (smallPrimesUpTo H).prod id := by
    rfl
  rw [heq]
  exact prod_dvd_prod_of_subset _ _ id (smallOddSupport_subset H n)

theorem factorization (H n m : ℕ) :
    squarefreeKernel n = smallOddPart H n * sourcePart H n m * residualPart H n m := by
  have hlarge : largeOddKernel H n = sourcePart H n m * residualPart H n m := by
    unfold largeOddKernel sourcePart residualPart sourceSupport residualSupport
    have h := prod_filter_mul_prod_filter_not ((oddPrimeSupport n).filter (H < ·)) (· ∣ m) id
    simpa only [filter_filter, not_and, and_assoc] using h.symm
  rw [← small_mul_large H n, hlarge, mul_assoc]

theorem kernel_mul_isSquare {n : ℕ} (hn : n ≠ 0) : IsSquare (squarefreeKernel n * n) := by
  use squarefreeKernel n * canonicalSquarePart n
  calc
    _ = squarefreeKernel n * (squarefreeKernel n * canonicalSquarePart n ^ 2) :=
      congrArg (squarefreeKernel n * ·) (squarefreeKernel_mul_squarePart hn).symm
    _ = _ := by ring

theorem square_equation (H m p : ℕ) (hm : m ≠ 0) (hp : p ≠ 0) :
    IsSquare ((smallOddPart H (m * p) * sourcePart H (m * p) m * residualPart H (m * p) m * m) * p) := by
  rw [← factorization H (m * p) m, mul_assoc]
  exact kernel_mul_isSquare (Nat.mul_ne_zero hm hp)

end PaperP1.RelativeSquarefreeParts
