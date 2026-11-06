module

public import PaperP1.Algebra.DerivationPowerEvaluation
public import Mathlib.FieldTheory.Finite.Basic

/-! # Actual finite-field Frobenius powers are constant for the derivation and agree at actual points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldDerivationFrobenius

open DerivationPowerEvaluation

variable {F A : Type*} [Field F] [Fintype F] [CommRing A] [Algebra F A]

theorem card_power_derivative_zero (D : Derivation F A A) (z : A) :
    D (z ^ Fintype.card F) = 0 := by
  have hq : (Fintype.card F : A) = 0 := by
    rw [← map_natCast (algebraMap F A), FiniteField.cast_card_eq_zero, map_zero]
  simp only [D.leibniz_pow, nsmul_eq_mul, smul_eq_mul, hq, zero_mul]

theorem iter_product_card_power (D : Derivation F A A) (g h : A) (r : ℕ) :
    iter D r (g * h ^ Fintype.card F) = iter D r g * h ^ Fintype.card F := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [iter_succ_left]
    rw [ih, D.leibniz, card_power_derivative_zero]
    simp only [smul_eq_mul, mul_zero, zero_add]
    exact mul_comm _ _

theorem evaluation_product_identity (D : Derivation F A A) (ε : A →ₐ[F] F) (g h : A) (r : ℕ) :
    ε (iter D r (g * h ^ Fintype.card F)) = ε (iter D r g * h) := by
  simp only [iter_product_card_power, map_mul, map_pow, FiniteField.pow_card]

theorem evaluation_sum_identity {ι : Type*} [Fintype ι]
    (D : Derivation F A A) (ε : A →ₐ[F] F) (c : ι → F) (g h : ι → A) (r : ℕ) :
    ε (iter D r (∑ i, c i • (g i * h i ^ Fintype.card F))) =
      ε (∑ i, c i • (iter D r (g i) * h i)) := by
  simp only [map_sum, map_smul, evaluation_product_identity]

end PaperP1.FiniteFieldDerivationFrobenius
