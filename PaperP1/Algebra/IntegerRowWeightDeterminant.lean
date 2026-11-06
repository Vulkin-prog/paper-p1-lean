module

public import PaperP1.Algebra.WeightedEvaluationDeterminant

/-! # An explicit integer determinant bound retaining every actual row weight -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerRowWeightDeterminant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem natAbs_bound (A : Matrix ι ι ℤ) (W : ι → ℕ) (hA : ∀ i j, |A i j| ≤ (W i : ℤ)) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * ∏ i, W i := by
  let φ := Int.castRingHom ℝ
  have hreal (i j : ι) : |φ (A i j)| ≤ (W i : ℝ) := by
    change |(A i j : ℝ)| ≤ (W i : ℝ)
    exact_mod_cast hA i j
  have hd := WeightedEvaluationDeterminant.row_weight_bound (φ.mapMatrix A) (fun i ↦ (W i : ℝ)) hreal
  rw [← RingHom.map_det] at hd
  change |(A.det : ℝ)| ≤ ((Fintype.card ι).factorial : ℝ) * ∏ i, (W i : ℝ) at hd
  have hint : |A.det| ≤ (((Fintype.card ι).factorial * ∏ i, W i : ℕ) : ℤ) := by exact_mod_cast hd
  rw [Int.abs_eq_natAbs] at hint
  exact_mod_cast hint

end PaperP1.IntegerRowWeightDeterminant
