module

public import PaperP1.Analysis.BinaryReductionBounds

/-! # Explicit integer coefficient heights after the actual basis shear -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryMatrixProductHeight

open PaperP1.BinaryBasisShear PaperP1.ReducedBinaryLatticeBasis PaperP1.BinaryEuclideanReduction

theorem product_height (A B : Matrix (Fin 2) (Fin 2) ℤ) (H K : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hB : ∀ i j, |B i j| ≤ (K : ℤ)) :
    ∀ i j, |(A * B) i j| ≤ ((2 * H * K : ℕ) : ℤ) := by
  intro i j
  exact UnimodularBinaryCoordinates.coordinate_height A H K (fun r ↦ B r j) hA (fun r ↦ hB r j) i

theorem shear_height (k : ℤ) (K : ℕ) (hk : |k| ≤ (K : ℤ)) :
    ∀ i j, |shear k i j| ≤ ((K + 1 : ℕ) : ℤ) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [shear] <;> linarith [Nat.cast_nonneg (α := ℤ) K]

theorem sheared_heights (A B : Matrix (Fin 2) (Fin 2) ℤ) (H K : ℕ) (k : ℤ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hB : ∀ i j, |B i j| ≤ (H : ℤ)) (hk : |k| ≤ (K : ℤ)) :
    (∀ i j, |(A * shear k) i j| ≤ ((2 * H * (K + 1) : ℕ) : ℤ)) ∧
      ∀ i j, |(shear (-k) * B) i j| ≤ ((2 * H * (K + 1) : ℕ) : ℤ) := by
  refine ⟨product_height A (shear k) H (K + 1) hA (shear_height k K hk), ?_⟩
  have hneg : |-k| ≤ (K : ℤ) := by simpa only [abs_neg] using hk
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    product_height (shear (-k)) B (K + 1) H (shear_height (-k) K hneg) hB

theorem reduced_heights (T : Matrix (Fin 2) (Fin 2) ℝ) (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (H K : ℕ) (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hB : ∀ i j, |B i j| ≤ (H : ℤ))
    (hk : |multiple (PaperP1.BinaryLatticeMinimum.realImage T (fun i ↦ A i 0))
      (PaperP1.BinaryLatticeMinimum.realImage T (fun i ↦ A i 1))| ≤ (K : ℤ)) :
    (∀ i j, |reduced T A i j| ≤ ((2 * H * (K + 1) : ℕ) : ℤ)) ∧
      ∀ i j, |reducedInverse T A B i j| ≤ ((2 * H * (K + 1) : ℕ) : ℤ) :=
  sheared_heights A B H K _ hA hB hk

end PaperP1.BinaryMatrixProductHeight
