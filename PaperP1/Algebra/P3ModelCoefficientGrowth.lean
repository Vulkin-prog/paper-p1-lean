module

public import PaperP1.Algebra.P3HeightControlledEquation

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3ModelCoefficientGrowth

open P3HomogeneousCoefficientFamily

def constant (d : ℕ) : ℕ := (3 * Fintype.card (Index d)) ^ (Fintype.card (Index d) - 1)

def exponent (d : ℕ) : ℕ := d * (Fintype.card (Index d) - 1)

theorem constant_pos (d : ℕ) : 0 < constant d :=
  pow_pos (Nat.mul_pos (by omega) (P3HomogeneousIntegerInterpolation.index_card_pos d)) _

theorem bound_eq (d H : ℕ) :
    (3 * Fintype.card (Index d) * H ^ d) ^ (Fintype.card (Index d) - 1) =
      constant d * H ^ exponent d := by
  rw [mul_pow, ← pow_mul]
  rfl

theorem certificate_growth (d T N H : ℕ) :
    T * (constant d * H ^ exponent d) ^ N =
      (T * constant d ^ N) * H ^ (exponent d * N) := by
  rw [mul_pow, ← pow_mul, Nat.mul_assoc]

end PaperP1.P3ModelCoefficientGrowth
