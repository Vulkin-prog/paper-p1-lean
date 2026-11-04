module

public import PaperP1.Arithmetic.BinaryBasisShear

/-! # Every column of an actual integer basis is primitive, including both axes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveBinaryColumns

theorem column_primitive (A B : Matrix (Fin 2) (Fin 2) ℤ) (hBA : B * A = 1) (j : Fin 2) :
    (A 0 j).natAbs.Coprime (A 1 j).natAbs := by
  apply (UnimodularBinaryCoordinates.primitive_iff_isCoprime (fun i ↦ A i j)).mpr
  refine ⟨B j 0, B j 1, ?_⟩
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M j j) hBA
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using h

theorem first_axis_abs (z : Fin 2 → ℤ) (hz : (z 0).natAbs.Coprime (z 1).natAbs) (h0 : z 0 = 0) :
    |z 1| = 1 := by
  have h : (z 1).natAbs = 1 := by simpa only [h0, Int.natAbs_zero, Nat.coprime_zero_left] using hz
  rw [Int.abs_eq_natAbs, h, Nat.cast_one]

theorem second_axis_abs (z : Fin 2 → ℤ) (hz : (z 0).natAbs.Coprime (z 1).natAbs) (h1 : z 1 = 0) :
    |z 0| = 1 := by
  have h : (z 0).natAbs = 1 := by simpa only [h1, Int.natAbs_zero, Nat.coprime_zero_right] using hz
  rw [Int.abs_eq_natAbs, h, Nat.cast_one]

end PaperP1.PrimitiveBinaryColumns
