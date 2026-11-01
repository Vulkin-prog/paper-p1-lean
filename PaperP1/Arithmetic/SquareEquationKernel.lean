module

public import PaperP1.Arithmetic.SquarefreeKernelProducts

/-! # A split-product square equation fixes the actual squarefree kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareEquationKernel

open Finset PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate PaperP1.SquarefreeKernelProducts
  PaperP1.SplitOffsetProducts

theorem kernels_eq_of_square_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsquare : IsSquare (a * b)) : squarefreeKernel a = squarefreeKernel b := by
  obtain ⟨w, hw⟩ := hsquare
  have hempty : oddPrimeSupport (a * b) = ∅ := by
    rw [hw, ← pow_two, support_square]
  have hmul := support_mul a b ha hb
  rw [hempty] at hmul
  have heq : oddPrimeSupport a = oddPrimeSupport b := symmDiff_eq_empty.mp hmul.symm
  unfold squarefreeKernel
  rw [heq]

theorem integer_square_to_kernel (A : Finset ℤ) (n W : ℕ) (D : ℤ) (hD : D ≠ 0)
    (hWn : W < n) (hA : ∀ a ∈ A, a.natAbs ≤ W)
    (hsquare : IsSquare (D * ∏ a ∈ A, ((n : ℤ) + a))) :
    kernel A n = squarefreeKernel D.natAbs := by
  rw [← product_cast A n W hWn hA] at hsquare
  obtain ⟨w, hw⟩ := hsquare
  have habs : IsSquare (D.natAbs * product A n) := by
    refine ⟨w.natAbs, ?_⟩
    have h := congrArg Int.natAbs hw
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h
  exact (kernels_eq_of_square_mul (Int.natAbs_ne_zero.mpr hD)
    (product_pos A n W hWn hA).ne' habs).symm

end PaperP1.SquareEquationKernel
